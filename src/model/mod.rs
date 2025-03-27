use ethcontract::H160;

/// Erc20 token pair specified by two contract addresses.
#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TokenPair(H160, H160);

impl TokenPair {
    /// Create a new token pair from two addresses.
    /// The addresses must not be the equal.
    pub fn new(token_a: H160, token_b: H160) -> Option<Self> {
        match token_a.cmp(&token_b) {
            std::cmp::Ordering::Less => Some(Self(token_a, token_b)),
            std::cmp::Ordering::Equal => None,
            std::cmp::Ordering::Greater => Some(Self(token_b, token_a)),
        }
    }

    /// Used to determine if `token` is among the pair.
    pub fn contains(&self, token: &H160) -> bool {
        self.0 == *token || self.1 == *token
    }

    /// Returns the token in the pair which is not the one passed in, or None if
    /// token passed in is not part of the pair
    pub fn other(&self, token: &H160) -> Option<H160> {
        if &self.0 == token {
            Some(self.1)
        } else if &self.1 == token {
            Some(self.0)
        } else {
            None
        }
    }

    /// The first address is always the lower one.
    /// The addresses are never equal.
    pub fn get(&self) -> (H160, H160) {
        (self.0, self.1)
    }

    /// Lowest element according to Ord trait.
    pub fn first_ord() -> Self {
        Self(
            H160([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
            H160([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
        )
    }
}

impl Default for TokenPair {
    fn default() -> Self {
        Self::new(H160::from_low_u64_be(0), H160::from_low_u64_be(1)).unwrap()
    }
}

impl IntoIterator for TokenPair {
    type IntoIter = std::iter::Chain<std::iter::Once<H160>, std::iter::Once<H160>>;
    type Item = H160;

    fn into_iter(self) -> Self::IntoIter {
        std::iter::once(self.0).chain(std::iter::once(self.1))
    }
}

impl<'a> IntoIterator for &'a TokenPair {
    type IntoIter = std::iter::Chain<std::iter::Once<&'a H160>, std::iter::Once<&'a H160>>;
    type Item = &'a H160;

    fn into_iter(self) -> Self::IntoIter {
        std::iter::once(&self.0).chain(std::iter::once(&self.1))
    }
}