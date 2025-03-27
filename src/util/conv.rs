//! Conversion utilities.

use {
    crate::domain::eth,
    bigdecimal::{num_bigint::ToBigInt, BigDecimal, Zero},
    ethereum_types::U256,
    num::{rational::Ratio, BigInt, BigUint, One},
    anyhow::Result,
};

pub trait U256Ext: Sized {
    fn to_big_int(&self) -> num::BigInt;
    fn to_big_uint(&self) -> num::BigUint;
    fn to_big_rational(&self) -> num::BigRational;

    fn checked_ceil_div(&self, other: &Self) -> Option<Self>;
    fn ceil_div(&self, other: &Self) -> Self;

    fn from_big_int(input: &num::BigInt) -> Result<Self>;
    fn from_big_uint(input: &num::BigUint) -> Result<Self>;
    fn from_big_rational(value: &num::BigRational) -> Result<Self>;
}

impl U256Ext for eth::U256 {
    fn to_big_int(&self) -> num::BigInt {
        num::BigInt::from_biguint(num::bigint::Sign::Plus, self.to_big_uint())
    }

    fn to_big_uint(&self) -> num::BigUint {
        let mut bytes = [0; 32];
        self.to_big_endian(&mut bytes);
        num::BigUint::from_bytes_be(&bytes)
    }

    fn to_big_rational(&self) -> num::BigRational {
        num::BigRational::new(self.to_big_int(), 1.into())
    }

    fn checked_ceil_div(&self, other: &Self) -> Option<Self> {
        self.checked_add(other.checked_sub(1.into())?)?
            .checked_div(*other)
    }

    fn ceil_div(&self, other: &Self) -> Self {
        self.checked_ceil_div(other)
            .expect("ceiling division arithmetic error")
    }

    fn from_big_int(input: &num::BigInt) -> Result<eth::U256> {
        anyhow::ensure!(input.sign() != num::bigint::Sign::Minus, "negative");
        Self::from_big_uint(input.magnitude())
    }

    fn from_big_uint(input: &num::BigUint) -> Result<Self> {
        let bytes = input.to_bytes_be();
        anyhow::ensure!(bytes.len() <= 32, "too large");
        Ok(eth::U256::from_big_endian(&bytes))
    }

    fn from_big_rational(value: &num::BigRational) -> Result<Self> {
        anyhow::ensure!(*value.denom() != num::BigInt::zero(), "zero denominator");
        Self::from_big_int(&(value.numer() / value.denom()))
    }
}

/// Converts a `BigDecimal` value to a `eth::Rational` value. Returns `None` if
/// the specified decimal value cannot be represented as a rational of `U256`
/// integers.
pub fn decimal_to_rational(d: &BigDecimal) -> Option<eth::Rational> {
    let (int, exp) = d.as_bigint_and_exponent();

    // First convert to a `Ratio<BigUint>`. This ensures that the ratio is
    // normalized (i.e. GCD of numerator and denomninator is 1) before trying to
    // convert the components to `U256`s. This allows values like `1.00...000`
    // that would otherwise overflow a `U256` numerator.
    let uint = int.to_biguint()?;
    let factor = BigUint::from(10_u8).pow(exp.unsigned_abs().try_into().ok()?);
    let ratio = if exp >= 0 {
        Ratio::new(uint, factor)
    } else {
        Ratio::new(uint * factor, num::one())
    };

    let numer = biguint_to_u256(ratio.numer())?;
    let denom = biguint_to_u256(ratio.denom())?;

    Some(eth::Rational::new_raw(numer, denom))
}

pub fn rational_to_decimal(r: &eth::Rational) -> BigDecimal {
    let exp = r.denom().to_f64_lossy().log10() as i64;
    BigDecimal::new(r.numer().to_big_int(), -exp)
}

pub fn biguint_to_u256(i: &BigUint) -> Option<U256> {
    let bytes = i.to_bytes_be();
    if bytes.len() > 32 {
        return None;
    }
    Some(U256::from_big_endian(&bytes))
}

pub fn u256_to_biguint(i: &U256) -> BigUint {
    let mut bytes = [0_u8; 32];
    i.to_big_endian(&mut bytes);
    BigUint::from_bytes_be(&bytes)
}

pub fn u256_to_bigdecimal(i: &U256) -> BigDecimal {
    BigDecimal::new(u256_to_biguint(i).into(), 0)
}

pub fn bigint_to_u256(i: &BigInt) -> Option<U256> {
    if i.sign() == num::bigint::Sign::Minus {
        return None;
    }
    biguint_to_u256(i.magnitude())
}

pub fn bigdecimal_to_u256(d: &BigDecimal) -> Option<U256> {
    let d = d.to_bigint()?;
    bigint_to_u256(&d)
}

/// Converts a `BigDecimal` amount in Ether units to wei.
pub fn decimal_to_ether(d: &BigDecimal) -> Option<eth::Ether> {
    let scaled = d * BigDecimal::new(BigInt::one(), -18);
    let ratio = decimal_to_rational(&scaled)?;
    Some(eth::Ether(ratio.numer() / ratio.denom()))
}

/// Converts an `eth::Ether` amount into a `BigDecimal` representation.
pub fn ether_to_decimal(e: &eth::Ether) -> BigDecimal {
    BigDecimal::new(u256_to_biguint(&e.0).into(), 18)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decimal_to_rational_conversions() {
        for (value, numer, denom) in [
            ("4.2", 21, 5),
            (
                "1000.00000000000000000000000000000000000000000000000000000000000\
                 0000000000000000000000000000000000000000000000000000000000000000",
                1000,
                1,
            ),
            ("0.003", 3, 1000),
        ] {
            let result = decimal_to_rational(&value.parse().unwrap()).unwrap();
            assert_eq!(result.numer().as_u64(), numer);
            assert_eq!(result.denom().as_u64(), denom);
        }
    }

    #[test]
    fn invalid_decimal_to_rational_conversions() {
        for value in [
            // negative
            "-0.42",
            // overflow numerator
            "1111111111111111111111111111111111111111111111111111111111111111111111111111111.1",
            // overflow denominator
            "0.0000000000000000000000000000000000000000000000000000000000000000000000000000001",
        ] {
            let result = decimal_to_rational(&value.parse().unwrap());
            assert!(result.is_none());
        }
    }

    #[test]
    fn decimal_to_and_from_ether() {
        for (decimal, ether) in [
            ("0.01", 10_000_000_000_000_000_u128),
            ("4.20", 4_200_000_000_000_000_000),
            ("10", 10_000_000_000_000_000_000),
        ] {
            let decimal = decimal.parse().unwrap();
            let ether = eth::Ether(ether.into());

            assert_eq!(decimal_to_ether(&decimal).unwrap(), ether);
            assert_eq!(ether_to_decimal(&ether), decimal);
        }
    }
}
