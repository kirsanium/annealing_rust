use crate::domain::eth::{H160, U256};
use num_bigint::BigUint;
use tycho_simulation::tycho_core::hex_bytes::Bytes;

pub fn u256_to_biguint(value: &U256) -> BigUint {
    let mut bytes = [0u8; 32];
    value.to_big_endian(&mut bytes);
    BigUint::from_bytes_be(&bytes)
}

pub fn biguint_to_u256(value: &BigUint) -> U256 {
    U256::from_big_endian(&value.to_bytes_be())
}

pub fn bytes_to_h160(value: &Bytes) -> H160 {
    H160::from_slice(value.0.iter().as_slice())
}

pub fn h160_to_bytes(value: &H160) -> Bytes {
    Bytes::from(value.as_bytes())
}

pub fn to_hex_str(token: H160) -> String {
    format!("{:#x}", token)
}
