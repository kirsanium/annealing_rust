use super::algorithm::{BasePool, AnnealingError};
use std::str::FromStr;
use crate::boundary::baseline::OnchainLiquidity;
use ethcontract::{H160, U256};

impl BasePool for OnchainLiquidity {
    fn get_amount_out(&self, token_in: &str, token_out: &str, amount_in: U256) -> Result<U256, AnnealingError> {
        let token_in = H160::from_str(token_in).map_err(|_| AnnealingError::GetAmountOut(format!("invalid token_in: {}", token_in)))?;
        let token_out = H160::from_str(token_out).map_err(|_| AnnealingError::GetAmountOut(format!("invalid token_out: {}", token_out)))?;
        let result = self.get_amount_out(
            token_out, 
            (amount_in, token_in)
        ).map_err(|_| AnnealingError::GetAmountOut(format!("failed to get amount out for pool: {}", self.id)))?;

        Ok(result)
    }

    fn get_id(&self) -> String {
        self.id.clone()
    }

    fn get_tokens(&self) -> (String, String) {
        (format!("{:#x}", self.token_pair.get().0), format!("{:#x}", self.token_pair.get().1))
    }
}
