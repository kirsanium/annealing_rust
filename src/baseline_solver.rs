//! Module containing basic path-finding logic to get quotes/routes for the best
//! onchain liquidity.

use std::sync::Arc;
use {
    ethcontract::{H160, U256},
    crate::model::TokenPair,
    std::collections::{HashMap, HashSet},
};
use derive_more::Display;
use itertools::Itertools;

/// The maximum number of hops to use when trading with AMMs along a path.
const DEFAULT_MAX_HOPS: usize = 2;

type PathCandidate = Vec<H160>;

/// Note that get_amount_out and get_amount_in are not always symmetrical. That
/// is for some AMMs it is possible that get_amount_out returns an amount for
/// which get_amount_in returns None when trying to go the reverse direction. Or
/// that the resulting amount is different from the original. This situation is
/// rare and resulting amounts should usually be identical or very close but it
/// can occur.
pub trait BaselineSolvable {
    // Given the desired output token, the amount and token input, return the
    // expected amount of output token.
    fn get_amount_out(&self, out_token: H160, input: (U256, H160)) -> Result<U256, BaselineSolverError>;

    // Given the input token, the amount and token we want output, return the
    // required amount of input token that needs to be provided.
    fn get_amount_in(&self, in_token: H160, output: (U256, H160)) -> Result<U256, BaselineSolverError>;

    // Given the desired output token, the amount and token input, return the
    // top estimate of the expected amount of output token.
    fn get_approx_amount_out(&self, out_token: H160, input: (U256, H160)) -> Result<U256, BaselineSolverError> {
        self.get_amount_out(out_token, input)
    }

    // Given the input token, the amount and token we want output, return the
    // required amount of input token that needs to be provided.
    fn get_approx_amount_in(&self, in_token: H160, out: (U256, H160)) -> Result<U256, BaselineSolverError> {
        self.get_amount_in(in_token, out)
    }

    // Returns the approximate amount of gas that using this piece of liquidity
    // would incur
    fn gas_cost(&self) -> usize;
}

#[derive(Debug, Clone)]
pub enum EstimateSide {
    Buy,
    Sell,
}

#[derive(Debug, Clone)]
pub struct Estimate<V, L> {
    // The result amount of the estimate
    pub value: V,
    // The liquidity path used to derive at that estimate
    pub path: Vec<Arc<L>>,
    // The side of the estimate
    pub side: EstimateSide,
}

impl<V, L: BaselineSolvable> Estimate<V, L> {
    pub fn gas_cost(&self) -> usize {
        // This could be more accurate by actually simulating the settlement (since
        // different tokens might have more or less expensive transfer costs)
        // For the standard OZ token the cost is roughly 110k for a direct trade, 170k
        // for a 1 hop trade, 230k for a 2 hop trade.
        let cost_of_hops: usize = self.path.iter().map(|item| item.gas_cost()).sum();
        50_000 + cost_of_hops
    }
}

pub fn find_all_buy_estimates<L: BaselineSolvable>(
    sell_amount: U256,
    path: &[H160],
    liquidity: &HashMap<TokenPair, Vec<Arc<L>>>,
    top_pools: usize,
) -> Vec<Estimate<U256, L>> {
    let sell_token = match path.first() {
        Some(token) => token,
        None => return Vec::new(),
    };
    
    // Helper function to recursively explore all paths
    fn explore_paths<L: BaselineSolvable>(
        amount: U256,
        current_token: H160,
        remaining_path: &[H160],
        liquidity: &HashMap<TokenPair, Vec<Arc<L>>>,
        current_path: Vec<Arc<L>>,
        top_pools: usize,
    ) -> Vec<Estimate<U256, L>> {
        if remaining_path.is_empty() {
            return vec![Estimate {
                value: amount,
                path: current_path,
                side: EstimateSide::Sell,
            }];
        }

        let next_token = remaining_path[0];
        let pair = match TokenPair::new(next_token, current_token) {
            Some(pair) => pair,
            None => return Vec::new(),
        };
        
        let pools = match liquidity.get(&pair) {
            Some(pools) => pools,
            None => return Vec::new(),
        };

        pools.into_iter()
            .filter_map(|pool| {
                if let Ok(out_amount) = pool.get_amount_out(next_token, (amount, current_token)) {
                    let mut new_path = current_path.clone();
                    new_path.push(Arc::clone(pool));
                    Some((out_amount, new_path))
                } else {
                    None
                }
            })
            .sorted_by_key(|(amount, _)| *amount)
            .rev()
            .take(top_pools)
            .map(|(amount, path)|
                explore_paths(
                    amount,
                    next_token,
                    &remaining_path[1..],
                    liquidity,
                    path,
                    top_pools,
                )
            )
            .flatten()
            .collect()
    }

    // Start the exploration and find the best result
    explore_paths(
        sell_amount,
        *sell_token,
        &path[1..],
        liquidity,
        Vec::new(),
        top_pools,
    )
    .into_iter()
    .sorted_by_key(|estimate| estimate.value)
    .rev()
    .collect()
}

// Given a path and sell amount (first token of the path) estimates the buy
// amount (last token of the path) and the path of liquidity that yields this
// result Returns None if the path is invalid or pool information doesn't exist.
pub fn estimate_buy_amount<L: BaselineSolvable>(
    sell_amount: U256,
    path: &[H160],
    liquidity: &HashMap<TokenPair, Vec<Arc<L>>>,
) -> Option<Estimate<U256, L>> {
    let sell_token = path.first()?;
    path.iter()
        .skip(1)
        .try_fold(
            (sell_amount, *sell_token, Vec::new()),
            |previous, current| {
                let (amount, previous, mut path) = previous;
                let (best_liquidity, amount) = liquidity
                    .get(&TokenPair::new(*current, previous)?)?
                    .iter()
                    .filter_map(|liquidity| {
                        Some((
                            liquidity,
                            liquidity.get_amount_out(*current, (amount, previous)).ok()?,
                        ))
                    })
                    .max_by_key(|(_, amount)| *amount)?;
                path.push(best_liquidity);
                Some((amount, *current, path))
            },
        )
        .map(|(amount, _, liquidity)| Estimate {
            value: amount,
            path: liquidity
                .into_iter()
                .map(Arc::clone)
                .collect(),
            side: EstimateSide::Sell,
        })
}

pub fn find_all_sell_estimates<L: BaselineSolvable>(
    buy_amount: U256,
    path: &[H160],
    liquidity: &HashMap<TokenPair, Vec<Arc<L>>>,
    top_pools: usize,
) -> Vec<Estimate<U256, L>> {
    let buy_token = match path.last() {
        Some(token) => token,
        None => return Vec::new(),
    };
    
    // Helper function to recursively explore all paths
    fn explore_paths<L: BaselineSolvable>(
        amount: U256,
        current_token: H160,
        remaining_path: &[H160],
        liquidity: &HashMap<TokenPair, Vec<Arc<L>>>,
        current_path: Vec<Arc<L>>,
        top_pools: usize,
    ) -> Vec<Estimate<U256, L>> {
        if remaining_path.is_empty() {
            return vec![Estimate {
                value: amount,
                path: current_path.into_iter().rev().collect(),
                side: EstimateSide::Buy,
            }];
        }

        let next_token = remaining_path[0];
        let pair = match TokenPair::new(next_token, current_token) {
            Some(pair) => pair,
            None => return Vec::new(),
        };
        
        let pools = match liquidity.get(&pair) {
            Some(pools) => pools,
            None => return Vec::new(),
        };
        
        pools.into_iter()
            .filter_map(|pool| {
                if let Ok(in_amount) = pool.get_amount_in(next_token, (amount, current_token)) {
                    let mut new_path = current_path.clone();
                    new_path.push(Arc::clone(pool));
                    Some((in_amount, new_path))
                } else {
                    None
                }
            })
            .sorted_by_key(|(amount, _)| *amount)
            .take(top_pools)
            .map(|(amount, path)|
                explore_paths(
                    amount,
                    next_token,
                    &remaining_path[1..],
                    liquidity,
                    path,
                    top_pools,
                )
            )
            .flatten()
            .collect()
    }

    // Start the exploration with reversed path (since we're going backwards)
    let reversed_path: Vec<_> = path.iter().rev().skip(1).copied().collect();
    explore_paths(
        buy_amount,
        *buy_token,
        &reversed_path,
        liquidity,
        Vec::new(),
        top_pools,
    )
    .into_iter()
    .sorted_by_key(|estimate| estimate.value)
    .collect()
}

// Given a path and buy amount (last token of the path) estimates the sell
// amount (first token of the path) and the path of liquidity that yields this
// result Returns None if the path is invalid or pool information doesn't exist.
pub fn estimate_sell_amount<L: BaselineSolvable>(
    buy_amount: U256,
    path: &[H160],
    liquidity: &HashMap<TokenPair, Vec<Arc<L>>>,
) -> Option<Estimate<U256, L>> {
    let buy_token = path.last()?;
    path.iter()
        .rev()
        .skip(1)
        .try_fold((buy_amount, *buy_token, Vec::new()), |previous, current| {
            let (amount, previous, mut path) = previous;
            let (best_liquidity, amount) = liquidity
                .get(&TokenPair::new(*current, previous)?)?
                .iter()
                .filter_map(|liquidity| {
                    Some((
                        liquidity,
                        liquidity.get_amount_in(*current, (amount, previous)).ok()?,
                    ))
                })
                .min_by_key(|(_, amount)| *amount)?;
            path.push(best_liquidity);
            Some((amount, *current, path))
        })
        .map(|(amount, _, liquidity)| Estimate {
            value: amount,
            // Since we reversed the path originally, we need to re-reverse it here.
            path: liquidity
                .into_iter()
                .rev()
                .map(Arc::clone)
                .collect(),
            side: EstimateSide::Buy,
        })
}

pub struct BaseTokens {
    /// The base tokens used to determine potential paths in the baseline
    /// solver.
    ///
    /// Always includes the native token.
    tokens: HashSet<H160>,
    /// All pairs of above.
    pairs: HashSet<TokenPair>,
}

impl BaseTokens {
    pub fn new(native_token: H160, base_tokens: &[H160]) -> Self {
        let mut tokens = base_tokens.to_vec();
        tokens.push(native_token);
        tokens.sort();
        tokens.dedup();
        let pairs = base_token_pairs(&tokens).collect();
        Self {
            tokens: tokens.into_iter().collect(),
            pairs,
        }
    }

    pub fn tokens(&self) -> &HashSet<H160> {
        &self.tokens
    }

    /// All pool token pairs that could be used along a path candidate for these
    /// token pairs.
    pub fn relevant_pairs(&self, pairs: impl Iterator<Item = TokenPair>) -> HashSet<TokenPair> {
        let mut result = HashSet::new();
        for pair in pairs {
            result.insert(pair);
            for token in pair {
                result.extend(
                    self.tokens
                        .iter()
                        .filter_map(move |base_token| TokenPair::new(*base_token, token)),
                );
            }
        }
        // Could be empty if the input pairs are empty. Just like path_candidates we
        // return empty set in this case.
        if !result.is_empty() {
            result.extend(self.pairs.iter().copied());
        }
        result
    }

    // Returns possible paths from sell_token to buy token, given a list of
    // potential intermediate base tokens and a maximum number of intermediate
    // steps. Can contain token pairs between base tokens or a base token and
    // the sell or buy token.
    pub fn path_candidates(&self, sell_token: H160, buy_token: H160) -> HashSet<PathCandidate> {
        self.path_candidates_with_hops(sell_token, buy_token, DEFAULT_MAX_HOPS)
    }

    /// Returns possible path candidates with the specified number of maximum
    /// hops.
    pub fn path_candidates_with_hops(
        &self,
        sell_token: H160,
        buy_token: H160,
        max_hops: usize,
    ) -> HashSet<PathCandidate> {
        path_candidates(sell_token, buy_token, &self.tokens, max_hops)
    }
}

fn path_candidates(
    sell_token: H160,
    buy_token: H160,
    base_tokens: &HashSet<H160>,
    max_hops: usize,
) -> HashSet<PathCandidate> {
    if sell_token == buy_token {
        return HashSet::new();
    }

    let mut candidates = HashSet::new();

    // Start with just the sell token (yields the direct pair candidate in the 0th
    // iteration)
    let mut path_prefixes = vec![vec![sell_token]];
    for _ in 0..(max_hops + 1) {
        let mut next_round_path_prefixes = vec![];
        for path_prefix in &path_prefixes {
            // For this round, add the buy token and path to the candidates
            let mut full_path = path_prefix.clone();
            full_path.push(buy_token);
            candidates.insert(full_path);

            // For the next round, amend current prefix with all base tokens that are not
            // yet on the path
            for base_token in base_tokens {
                if base_token != &buy_token && !path_prefix.contains(base_token) {
                    let mut next_round_path_prefix = path_prefix.clone();
                    next_round_path_prefix.push(*base_token);
                    next_round_path_prefixes.push(next_round_path_prefix);
                }
            }
        }
        path_prefixes = next_round_path_prefixes;
    }
    candidates
}

/// All token pairs between base tokens.
fn base_token_pairs(base_tokens: &[H160]) -> impl Iterator<Item = TokenPair> + '_ {
    base_tokens
        .iter()
        .copied()
        .enumerate()
        .flat_map(move |(index, token)| {
            base_tokens
                .iter()
                .copied()
                .skip(index)
                .filter_map(move |token_| TokenPair::new(token, token_))
        })
}

#[derive(Debug, Display)]
pub enum BaselineSolverError {
    #[display(fmt = "Amount calculation failed: {}", _0)]
    AmountCalculation(String),
    #[display(fmt = "Invalid token: {}", _0)] 
    InvalidToken(String),
    #[display(fmt = "Pool error: {}", _0)]
    Pool(String),
}
