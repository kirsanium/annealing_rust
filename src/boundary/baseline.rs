use crate::boundary;
use ethcontract::{H160, U256};
use crate::model::TokenPair;
use derive_more::Display;
use crate::baseline_solver::{BaselineSolvable, BaselineSolverError};

#[derive(Debug, Clone)]
pub struct OnchainLiquidity {
    pub id: String,
    pub token_pair: TokenPair,
    pub source: LiquiditySource,
}

#[derive(Debug, Clone)]
pub enum LiquiditySource {
    ConstantProduct(boundary::liquidity::constant_product::Pool),
    Concentrated(boundary::liquidity::concentrated::ConcentratedPool),
}

impl OnchainLiquidity {
    pub fn get_amount_out(&self, out_token: H160, input: (U256, H160)) -> Result<U256, BaselineSolverError> {
        Ok(match &self.source {
            LiquiditySource::ConstantProduct(pool) => pool.get_amount_out(out_token, input)?,
            LiquiditySource::Concentrated(pool) => pool.get_amount_out(out_token, input)?,
        })
    }

    pub fn get_amount_in(&self, in_token: H160, output: (U256, H160)) -> Result<U256, BaselineSolverError> {
        Ok(match &self.source {
            LiquiditySource::ConstantProduct(pool) => pool.get_amount_in(in_token, output)?,
            LiquiditySource::Concentrated(pool) => pool.get_amount_in(in_token, output)?,
        })
    }

    pub fn get_approx_amount_out(&self, out_token: H160, input: (U256, H160)) -> Result<U256, BaselineSolverError> {
        Ok(match &self.source {
            LiquiditySource::ConstantProduct(pool) => pool.get_approx_amount_out(out_token, input)?,
            LiquiditySource::Concentrated(pool) => pool.get_approx_amount_out(out_token, input)?,
        })
    }

    pub fn get_approx_amount_in(&self, in_token: H160, output: (U256, H160)) -> Result<U256, BaselineSolverError> {
        Ok(match &self.source {
            LiquiditySource::ConstantProduct(pool) => pool.get_approx_amount_in(in_token, output)?,
            LiquiditySource::Concentrated(pool) => pool.get_approx_amount_in(in_token, output)?,
        })
    }

    pub fn gas_cost(&self) -> usize {
        match &self.source {
            LiquiditySource::ConstantProduct(pool) => pool.gas_cost(),
            LiquiditySource::Concentrated(pool) => pool.gas_cost(),
        }
    }
}
