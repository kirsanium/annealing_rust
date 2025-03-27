use {crate::domain::{liquidity, eth}, ethereum_types::{H160, U256}};
use crate::model::TokenPair;
use num::rational::Ratio;
use derive_more::Display;
use crate::baseline_solver::{BaselineSolverError, BaselineSolvable};

/// Converts a domain pool into a [`shared`] Uniswap V2 pool. Returns `None` if
/// the domain pool cannot be represented as a boundary pool.
pub fn to_boundary_pool(address: H160, pool: &liquidity::constant_product::Pool) -> Option<Pool> {
    let reserves = pool.reserves.get();
    let tokens = TokenPair::new(reserves.0.token.0, reserves.1.token.0)
        .expect("tokens are distinct by construction");

    // reserves are ordered by construction.
    let reserves = (reserves.0.amount.as_u128(), reserves.1.amount.as_u128());

    if *pool.fee.numer() > u32::MAX.into() || *pool.fee.denom() > u32::MAX.into() {
        return None;
    }
    let fee = num::rational::Ratio::new(pool.fee.numer().as_u32(), pool.fee.denom().as_u32());

    Some(Pool {
        address,
        tokens,
        reserves,
        fee,
    })
}

pub const POOL_SWAP_GAS_COST: usize = 90171;

lazy_static::lazy_static! {
    static ref POOL_MAX_RESERVES: U256 = U256::from((1u128 << 112) - 1);
}

/// This type denotes `(reserve_a, reserve_b, token_b)` where
/// `reserve_a` refers to the reserve of the excluded token.
type RelativeReserves = (U256, U256, H160);

#[derive(Clone, Copy, Eq, Hash, PartialEq, Debug)]
pub struct Pool {
    pub address: H160,
    pub tokens: TokenPair,
    pub reserves: (u128, u128),
    pub fee: Ratio<u32>,
}

impl Pool {
    pub fn uniswap(address: H160, tokens: TokenPair, reserves: (u128, u128)) -> Self {
        Self {
            address,
            tokens,
            reserves,
            fee: Ratio::new(3, 1000),
        }
    }

    /// Given an input amount and token, returns the maximum output amount and
    /// address of the other asset. Returns error if operation not possible
    /// due to arithmetic issues (e.g. over or underflow)
    fn get_amount_out(&self, token_in: H160, amount_in: U256) -> Result<(U256, H160), BaselineSolverError> {
        let (reserve_in, reserve_out, token_out) = self.get_relative_reserves(token_in)
            .ok_or_else(|| BaselineSolverError::InvalidToken("Token not part of pool".into()))?;
        
        let amount_out = self.amount_out(amount_in, reserve_in, reserve_out)
            .map_err(|e| BaselineSolverError::AmountCalculation(e.0))?;
        Ok((amount_out, token_out))
    }

    /// Given an output amount and token, returns a required input amount and
    /// address of the other asset. Returns None if operation not possible
    /// due to arithmetic issues (e.g. over or underflow, reserve too small)
    fn get_amount_in(&self, token_out: H160, amount_out: U256) -> Result<(U256, H160), BaselineSolverError> {
        let (reserve_out, reserve_in, token_in) = self.get_relative_reserves(token_out)
            .ok_or_else(|| BaselineSolverError::InvalidToken("Token not part of pool".into()))?;
        
        let amount_in = self.amount_in(amount_out, reserve_in, reserve_out)
            .map_err(|e| BaselineSolverError::AmountCalculation(e.message().clone()))?;
        Ok((amount_in, token_in))
    }

    /// Given one of the pool's two tokens, returns a tuple containing the
    /// `RelativeReserves` along with the opposite token. That is, the
    /// elements returned are (respectively)
    /// - the pool's reserve of token provided
    /// - the reserve of the other token
    /// - the pool's other token
    /// This is essentially a helper method for shuffling values in
    /// `get_amount_in` and `get_amount_out`
    fn get_relative_reserves(&self, token: H160) -> Option<RelativeReserves> {
        // https://github.com/Uniswap/uniswap-v2-periphery/blob/master/contracts/libraries/UniswapV2Library.sol#L53
        if token == self.tokens.get().0 {
            Some((
                U256::from(self.reserves.0),
                U256::from(self.reserves.1),
                self.tokens.get().1,
            ))
        } else {
            if token != self.tokens.get().1 {
                return None;
            }
            Some((
                U256::from(self.reserves.1),
                U256::from(self.reserves.0),
                self.tokens.get().0,
            ))
        }
    }

    fn amount_out(&self, amount_in: U256, reserve_in: U256, reserve_out: U256) -> Result<U256, PoolError> {
        if amount_in.is_zero() {
            return Err(PoolError("Amount in is zero".into()));
        }
        if reserve_in.is_zero() {
            return Err(PoolError("Input reserve is zero".into()));
        }
        if reserve_out.is_zero() {
            return Err(PoolError("Output reserve is zero".into()));
        }

        let amount_in_with_fee =
            amount_in.checked_mul(
                U256::from(self.fee.denom()
                    .checked_sub(*self.fee.numer())
                    .ok_or_else(|| PoolError("Fee subtraction overflow".into()))?)
            )
            .ok_or_else(|| PoolError("Amount_in amplifications overflow".into()))?;
        let numerator = amount_in_with_fee
            .checked_mul(reserve_out)
            .ok_or_else(|| PoolError("Reserve multiplication overflow".into()))?;

        let denominator = reserve_in
            .checked_mul(U256::from(*self.fee.denom()))
            .ok_or_else(|| PoolError("Reserve fee multiplication overflow".into()))?
            .checked_add(amount_in_with_fee)
            .ok_or_else(|| PoolError("Denominator addition overflow".into()))?;
        
        let amount_out = numerator
            .checked_div(denominator)
            .ok_or_else(|| PoolError("Division by zero in amount calculation".into()))?;
        
        check_final_reserves(amount_in, amount_out, reserve_in, reserve_out)
            .map(|_| amount_out)
            .ok_or_else(|| PoolError("Final reserves check failed".into()))
    }

    fn amount_in(&self, amount_out: U256, reserve_in: U256, reserve_out: U256) -> Result<U256, PoolError> {
        if amount_out.is_zero() {
            return Err(PoolError("Amount out is zero".into()));
        }
        if reserve_in.is_zero() {
            return Err(PoolError("Input reserve is zero".into()));
        }
        if reserve_out.is_zero() {
            return Err(PoolError("Output reserve is zero".into()));
        }

        let numerator = reserve_in
            .checked_mul(amount_out)
            .ok_or_else(|| PoolError("Reserve multiplication overflow".into()))?
            .checked_mul(U256::from(*self.fee.denom()))
            .ok_or_else(|| PoolError("Fee multiplication overflow".into()))?;

        let fee_numerator = self.fee.denom()
            .checked_sub(*self.fee.numer())
            .ok_or_else(|| PoolError("Fee subtraction overflow".into()))?;

        let denominator = reserve_out
            .checked_sub(amount_out)
            .ok_or_else(|| PoolError("Insufficient output reserve".into()))?
            .checked_mul(U256::from(fee_numerator))
            .ok_or_else(|| PoolError("Fee multiplication overflow".into()))?;

        let amount_in = numerator
            .checked_div(denominator)
            .ok_or_else(|| PoolError("Division by zero in amount calculation".into()))?
            .checked_add(1.into())
            .ok_or_else(|| PoolError("Amount addition overflow".into()))?;

        check_final_reserves(amount_in, amount_out, reserve_in, reserve_out)
            .map(|_| amount_in)
            .ok_or_else(|| PoolError("Final reserves check failed".into()))
    }
}

#[derive(Debug, Clone, Display)]
struct PoolError(String);

impl PoolError {
    pub fn message(&self) -> &String {
        &self.0
    }
}

fn check_final_reserves(
    amount_in: U256,
    amount_out: U256,
    reserve_in: U256,
    reserve_out: U256,
) -> Option<(U256, U256)> {
    let final_reserve_in = reserve_in.checked_add(amount_in)?;
    let final_reserve_out = reserve_out.checked_sub(amount_out)?;

    if final_reserve_in > *POOL_MAX_RESERVES {
        None
    } else {
        Some((final_reserve_in, final_reserve_out))
    }
}

impl BaselineSolvable for Pool {
    fn get_amount_out(&self, out_token: H160, (in_amount, in_token): (U256, H160)) -> Result<U256, BaselineSolverError> {
        let (out_amount, token) = self.get_amount_out(in_token, in_amount)?;
        if token != out_token {
            return Err(BaselineSolverError::InvalidToken(
                format!("Expected output token {}, got {}", out_token, token)
            ));
        }
        Ok(out_amount)
    }

    fn get_amount_in(&self, in_token: H160, (out_amount, out_token): (U256, H160)) -> Result<U256, BaselineSolverError> {
        let (in_amount, token) = self.get_amount_in(out_token, out_amount)?;
        if token != in_token {
            return Err(BaselineSolverError::InvalidToken(
                format!("Expected input token {}, got {}", in_token, token)
            ));
        }
        Ok(in_amount)
    }

    fn gas_cost(&self) -> usize {
        POOL_SWAP_GAS_COST
    }
}