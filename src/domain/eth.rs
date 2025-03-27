use derive_more::From;

pub use ethereum_types::{H160, H256, U256};

pub const ETH_TOKEN: TokenAddress = TokenAddress(H160([0xee; 20]));

/// A contract address.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ContractAddress(pub H160);

/// An ERC20 token address.
///
/// https://eips.ethereum.org/EIPS/eip-20
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TokenAddress(pub H160);

impl TokenAddress {
    /// If the token is ETH, return WETH, thereby "wrapping" it.
    pub fn wrap(self, weth: WethAddress) -> Self {
        if self == ETH_TOKEN {
            Self(weth.0)
        } else {
            self
        }
    }

    /// If the token is WETH, return ETH, thereby "unwrapping" it.
    pub fn unwrap(self, weth: WethAddress) -> Self {
        if self.0 == weth.0 {
            ETH_TOKEN
        } else {
            self
        }
    }
}

impl From<H160> for TokenAddress {
    fn from(inner: H160) -> Self {
        Self(inner)
    }
}

/// The WETH token (or equivalent) for the EVM compatible network.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WethAddress(pub H160);

/// An asset on the Ethereum blockchain. Represents a particular amount of a
/// particular token.
#[derive(Debug, Clone, Copy)]
pub struct Asset {
    pub amount: U256,
    pub token: TokenAddress,
}

/// An Ether amount in wei.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Ether(pub U256);

impl std::ops::Add for Ether {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl From<U256> for Ether {
    fn from(value: U256) -> Self {
        Self(value)
    }
}

/// A token amount in wei, always representing the sell token of an order.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, From)]
pub struct SellTokenAmount(pub U256);

/// Like [`Gas`] but can be negative to encode a gas discount.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct SignedGas(i64);

impl From<i64> for SignedGas {
    fn from(value: i64) -> Self {
        Self(value)
    }
}

/// Gas amount.
#[derive(Clone, Copy, Debug, Default)]
pub struct Gas(pub U256);

impl std::ops::Add for Gas {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl std::ops::Add<SignedGas> for Gas {
    type Output = Self;

    fn add(self, rhs: SignedGas) -> Self::Output {
        if rhs.0.is_positive() {
            Self(self.0.saturating_add(rhs.0.into()))
        } else {
            Self(self.0.saturating_sub(rhs.0.abs().into()))
        }
    }
}

impl std::ops::Sub<SignedGas> for Gas {
    type Output = Self;

    fn sub(self, rhs: SignedGas) -> Self::Output {
        if rhs.0.is_positive() {
            Self(self.0.saturating_sub(rhs.0.into()))
        } else {
            Self(self.0.saturating_add(rhs.0.abs().into()))
        }
    }
}

/// A 256-bit rational type.
pub type Rational = num::rational::Ratio<U256>;

/// An address. Can be an EOA or a smart contract address.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Address(pub H160);

impl From<H160> for Address {
    fn from(value: H160) -> Self {
        Self(value)
    }
}

impl From<Address> for H160 {
    fn from(value: Address) -> Self {
        value.0
    }
}
