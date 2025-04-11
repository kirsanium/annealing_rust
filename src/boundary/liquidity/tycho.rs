use tycho_simulation::models::Token;
use tycho_simulation::protocol::models::ProtocolComponent;
use tycho_simulation::protocol::state::ProtocolSim;
use std::sync::Arc;
use ethereum_types::{H160, U256};
use crate::util::tycho::{bytes_to_h160, u256_to_biguint, to_hex_str};
use derive_more::Display;

pub type TychoPoolState = Arc<dyn ProtocolSim>;

#[derive(Debug, Clone)]
pub struct TychoPool {
    pub component: ProtocolComponent,
    state: TychoPoolState,
    protocol: PoolProtocol,
    tokens_h160: Vec<H160>,
}

impl TychoPool {
    pub fn new(component: ProtocolComponent, state: TychoPoolState) -> Self {
        let tokens_h160 = component.tokens.iter().map(|token| bytes_to_h160(&token.address)).collect();
        let protocol = match component.protocol_system.as_str() {
            "uniswap_v2" => PoolProtocol::UniswapV2,
            "sushiswap_v2" => PoolProtocol::SushiswapV2,
            "pancakeswap_v2" => PoolProtocol::PancakeswapV2,
            "uniswap_v3" => PoolProtocol::UniswapV3,
            "uniswap_v4" => PoolProtocol::UniswapV4,
            "vm:balancer_v2" => PoolProtocol::BalancerV2,
            "vm:curve" => PoolProtocol::Curve,
            _ => panic!("Unknown pool protocol: {}", component.protocol_system),
        };
        Self { component, tokens_h160, state, protocol }
    }

    pub fn get_amount_out(&self, out_token: H160, input: (U256, H160)) -> Result<U256, TychoPoolCallError> {
        let amount_in = u256_to_biguint(&input.0);
        let token_in = self.component.tokens.iter()
            .find(|token| bytes_to_h160(&token.address) == input.1)
            .ok_or(TychoPoolCallError::InvalidToken)?;
        let token_out = self.component.tokens.iter()
            .find(|token| bytes_to_h160(&token.address) == out_token)
            .ok_or(TychoPoolCallError::InvalidToken)?;
        let amount = self.state
            .get_amount_out(amount_in, token_in, token_out)
            .map_err(|_| TychoPoolCallError::AmountOut)?
            .amount.to_bytes_be();
        Ok(U256::from_big_endian(&amount))
    }

    pub fn get_approx_amount_out(&self, out_token: H160, input: (U256, H160)) -> Result<U256, TychoPoolCallError> {
        let spot_price = self.spot_price(input.1, out_token)?;
        let amount = U256::from_f64_lossy(input.0.to_f64_lossy() * spot_price);
        Ok(amount)
    }

    pub fn get_approx_amount_in(&self, in_token: H160, output: (U256, H160)) -> Result<U256, TychoPoolCallError> {
        let spot_price = self.spot_price(in_token, output.1)?;
        let amount = U256::from_f64_lossy(output.0.to_f64_lossy() / spot_price);
        Ok(amount)
    }

    pub fn get_amount_in(&self, in_token: H160, output: (U256, H160)) -> Result<U256, TychoPoolCallError> {
        let right0 = self.get_right_border(in_token, output)
            .ok_or(TychoPoolCallError::AmountIn)?;
        let mut amount_in_right = right0;
        let mut amount_in_left = U256::zero();
        for _ in 0..20 {
            let mean_value = (amount_in_right + amount_in_left) / 2;
            let amount_out_at_mean = self.get_amount_out(output.1, (mean_value, in_token))?;
            (amount_in_left, amount_in_right) = Self::correct_left_right(
                amount_out_at_mean, output.0, amount_in_left, amount_in_right, mean_value);
        }
        Ok(amount_in_right)
    }

    pub fn spot_price(&self, in_token: H160, out_token: H160) -> Result<f64, TychoPoolCallError> {
        let token_in = self.token_by_address(in_token)?;
        let token_out = self.token_by_address(out_token)?;
        let spot_price = self.state.spot_price(token_in, token_out)
            .map_err(|_| TychoPoolCallError::AmountOut)?;
        Ok(spot_price)
    }

    pub fn get_tokens(&self) -> &Vec<H160> {
        &self.tokens_h160
    }

    pub fn id(&self) -> String {
        to_hex_str(self.address())
    }

    pub fn address(&self) -> H160 {
        let id_bytes = &self.component.id[..20];
        H160::from_slice(id_bytes)
    }

    pub fn protocol(&self) -> PoolProtocol {
        self.protocol
    }

    fn get_right_border(&self, in_token: H160, output: (U256, H160)) -> Option<U256> {
        // Проверяем сколько получим от обратного обмена, умножаем значение на 5
        let reverse_swap_value = self.get_amount_out(in_token, output).ok()?;
        let right0 = reverse_swap_value * U256::from(5);
        let big_amount_out = self.get_amount_out(output.1, (right0, in_token)).ok()?;
        if big_amount_out < output.0 {
            return None
        }
        Some(right0)
    }

    fn correct_left_right(
        amount_out_at_mean: U256,
        amount_out: U256,
        amount_in_left: U256,
        amount_in_right: U256,
        mean_value: U256,
    ) -> (U256, U256) {
        if amount_out_at_mean > amount_out
            {(amount_in_left, mean_value)}
        else
            {(mean_value, amount_in_right)}
    }

    fn token_by_address(&self, address: H160) -> Result<&Token, TychoPoolCallError> {
        self.component.tokens.iter()
            .find(|token| bytes_to_h160(&token.address) == address)
            .ok_or(TychoPoolCallError::InvalidToken)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum PoolProtocol {
    UniswapV2,
    SushiswapV2,
    PancakeswapV2,
    UniswapV3,
    UniswapV4,
    BalancerV2,
    Curve,
}

#[derive(Debug, Clone, Display)]
pub enum TychoPoolCallError {
    AmountOut,
    AmountIn,
    InvalidToken,
}