use rand::seq::SliceRandom;
use rand::{rng, Rng};
use rand_distr::{Distribution, LogNormal};
use std::collections::{HashMap, VecDeque, HashSet};
use std::time::{Instant, Duration};
use serde::Serialize;
use std::sync::Arc;
use serde_with::serde_as;
use ethcontract::U256;
use crate::util::serialize;
use std::fmt;
use itertools::Itertools;

pub type Pool = Arc<dyn BasePool>;
pub type PoolId = String;
pub type AnnealingResult = Result<Evaluation, AnnealingError>;
pub type Prices = HashMap<String, U256>;

#[serde_as]
#[derive(Debug, Clone, Serialize)]
pub struct Order {
    pub id: String,
    pub buy_token: String,
    pub sell_token: String,
    #[serde_as(as = "serialize::U256")]
    pub sell_amount: U256,
    #[serde_as(as = "serialize::U256")]
    pub buy_amount: U256,
    pub partial: bool,
    pub portion: f64
}

#[derive(Clone)]
struct Edge {
    target: usize,
    rate: f64,
    pool: Pool,
}

impl fmt::Debug for Edge {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Edge {{ target: {}, rate: {}, tokens: {:?} }}", self.target, self.rate, self.pool.get_tokens())
    }
}

pub trait BasePool: std::fmt::Debug + Sync + Send {
    fn get_amount_out(&self, token_in: &str, token_out: &str, amount_in: U256) -> Result<U256, AnnealingError>;
    fn get_id(&self) -> String;
    fn get_tokens(&self) -> (String, String);
}

#[derive(Debug, Clone, Default)]
pub struct AnnealingArgs {
    pub prices: Prices,
    pub pools: Vec<Pool>,
    pub orders: Vec<Order>,
    pub gas_price: U256,
}

pub struct Annealing;
impl Annealing {
    pub fn run(threads: usize, time_ms: u64, args: AnnealingArgs) -> AnnealingResult {
        let mut allowed_amounts = HashMap::new();
        let base_allowed_amounts = args.orders.iter().map(|o| (o.id.clone(), o.buy_amount)).collect::<HashMap<String, U256>>();
        let mut updated_orders: Vec<Order> = Vec::new();
        for order in &args.orders {
            let net = Net::new(args.prices.clone(), args.pools.clone(), vec![order.clone()], base_allowed_amounts.clone(), args.gas_price);
            if net.is_err() {
                return Err(AnnealingError::StartFailed);
            }
            // Было бы хорошо эту часть тоже распарлелить
            // То есть вновь запустить функцию во всех потоках и взять максимум
            let result = net.unwrap().run_simulation(10);
            let result2 = result.clone();
            let required_buy_amount = order.buy_amount + U256::exp10(32) / args.prices[&order.buy_token];
            if let Ok(eval) = result {
                if eval.metric > 0. {
                    let in_amount = eval.interactions
                        .iter()
                        .filter(|i| i.in_token_id == order.sell_token)
                        .map(|i| i.amount_in)
                        .fold(U256::from(0), |acc, i| acc + i);
                    let cur_portion = in_amount.to_f64_lossy() / order.sell_amount.to_f64_lossy();
                    if cur_portion < 0.000001{
                        allowed_amounts.insert(order.id.clone(), required_buy_amount);
                    }else{
                        let out_amount = eval.interactions
                            .iter()
                            .filter(|i| i.out_token_id == order.buy_token)
                            .map(|i| i.amount_out)
                            .fold(U256::from(0), |acc, i| acc + i);
                        allowed_amounts.insert(order.id.clone(), out_amount);
                    }
                } else {
                    allowed_amounts.insert(order.id.clone(), required_buy_amount);
                }
            } else {
                allowed_amounts.insert(order.id.clone(), required_buy_amount);
            }
            if order.partial {
                let mut new_order = order.clone();
                let mut cur_portion = 1.0;
                if let Ok(eval) = result2{
                    if eval.metric > 0.{
                        let in_amount = eval.interactions
                        .iter()
                        .filter(|i| i.in_token_id == order.sell_token)
                        .map(|i| i.amount_in)
                        .fold(U256::from(0), |acc, i| acc + i);
                        cur_portion = in_amount.to_f64_lossy() / new_order.sell_amount.to_f64_lossy();
                    }
                }
                println!("{}", cur_portion);
                if cur_portion < 0.000001{
                    cur_portion = 1.0;
                }
                println!("{}", cur_portion);
                new_order.buy_amount = if cur_portion == 1.0 {
                    order.buy_amount
                } else {
                    U256::from_f64_lossy(order.buy_amount.to_f64_lossy() * cur_portion)
                };
                new_order.sell_amount = if cur_portion == 1.0 {
                    order.sell_amount
                } else {
                    U256::from_f64_lossy(order.sell_amount.to_f64_lossy() * cur_portion)
                };
                new_order.partial = false;
                updated_orders.push(new_order);
            }else{
                updated_orders.push(order.clone());
            }
        }
        let args = AnnealingArgs {
            orders: updated_orders,
            ..args
        };
        let profits = args.orders.iter().map(|o| {
            (o.id.clone(), allowed_amounts[&o.id] - o.buy_amount)
        }).collect::<HashMap<_, _>>();

        allowed_amounts.iter_mut().for_each(|(id, amount)| {
            *amount = *amount - profits[id].checked_div(100.into()).unwrap();
        });
        let handles: Vec<_> = (0..threads).map(|_| {
            let args = args.clone();
            let allowed_amounts = allowed_amounts.clone();
            std::thread::spawn(move || {
                let mut net = Net::new(args.prices, args.pools, args.orders, allowed_amounts, args.gas_price)?;
                net.run_simulation(time_ms)
            })
        }).collect();

        handles.into_iter()
            .map(|h| h.join().unwrap())
            .flatten()
            .max_by(|a, b| a.metric.total_cmp(&b.metric))
            .ok_or(AnnealingError::StartFailed)
    }
}


#[derive(Debug, Clone, Default)]
pub struct Net {
    n: usize,
    edges: Vec<Vec<Edge>>,
    save_edges: Vec<Vec<Edge>>,
    topsort: Vec<usize>,
    prices: Vec<U256>,
    save_prices: Vec<U256>,
    init: Vec<U256>,
    target_required: Vec<U256>,
    target_default: Vec<U256>,
    currencies_to_int: HashMap<String, usize>,
    int_to_currencies: Vec<String>,
    prices_map: Prices,
    final_prices_map: Prices,
    orders: Vec<Order>,
    save_orders: Vec<Order>,
    evals_called: usize,
    gas_price: U256,
    allowed_amounts: HashMap<String, U256>,
}

#[derive(Debug, Clone)]
pub enum AnnealingError {
    NoPrice(String),
    GetAmountOut(String),
    NoEdges,
    EmptyNet,
    StartFailed,
}

#[derive(Debug, Clone)]
pub struct Evaluation {
    // Positive metric means better solution than the initial state.
    // The bigger the metric, the better the solution.
    pub metric: f64,
    pub interactions: Vec<Interaction>,
    pub orders: Vec<Order>,
    pub prices: Prices,
}

impl Net {
    pub fn new(prices: Prices, pools: Vec<Pool>, orders: Vec<Order>, allowed_amounts: HashMap<String, U256>, gas_price: U256) -> Result<Self, AnnealingError> {
        if orders.is_empty() {
            return Err(AnnealingError::EmptyNet);
        }
        let mut net = Net::default();
        net.gas_price = gas_price;
        net.allowed_amounts = allowed_amounts;
        for (token, price) in &prices {
            net.set_price(token.clone(), *price);
        }

        let pools = pools.into_iter()
            .sorted_by_key(|p| p.get_id())
            .dedup_by(|a, b| a.get_id() == b.get_id()).collect::<Vec<_>>();
        let orders = orders.into_iter()
            .sorted_by_key(|o| o.id.clone())
            .dedup_by(|a, b| a.id == b.id).collect::<Vec<_>>();

        let tokens = pools.iter().map(|p|
            vec![p.get_tokens().0, p.get_tokens().1]).flatten().collect::<HashSet<_>>();

        let order_tokens = orders.iter().map(|o|
            vec![o.sell_token.clone(), o.buy_token.clone()]).flatten().collect::<HashSet<_>>();

        let tokens = tokens.union(&order_tokens).collect::<HashSet<_>>();

        if tokens.is_empty() || pools.is_empty() {
            return Err(AnnealingError::EmptyNet);
        }

        println!("Creating net: {} tokens, {} orders", tokens.len(), orders.len());

        net.n = tokens.len();
        net.int_to_currencies.resize(net.n, String::new());
        net.prices = vec![U256::from(1); net.n];
        net.init = vec![U256::from(0); net.n];
        net.target_required = vec![U256::from(0); net.n];
        net.edges = vec![Vec::new(); net.n];
        for (i, address) in tokens.into_iter().enumerate() {
            net.currencies_to_int.insert(address.clone(), i);
            net.int_to_currencies[i] = address.clone();
            if net.prices_map.get(address).is_none() {
                return Err(AnnealingError::NoPrice(address.clone()));
            }
            net.prices[i] = net.prices_map[address];
        }
        net.save_prices = net.prices.clone();

        net.insert_pools(pools);
        net.set_orders(orders);
        net.reset_topsort(0.0);

        Ok(net)
    }

    pub fn run_simulation(&mut self, max_time_ms: u64) -> Result<Evaluation, AnnealingError> {
        let start = Instant::now();
        let mut rng = rng();
        
        let mut cur_eval: f64;
        let mut best_eval = f64::MIN;
        let init_n = self.clone();
        let mut best_n = self.clone();
        let mut count = 0;
        let any_partials = self.orders.iter().any(|o| o.partial);
        while start.elapsed() < Duration::from_millis(max_time_ms) {
            count = count + 1;
            println!("Starting new iteration");
            *self = init_n.clone();

            let elapsed_ms = start.elapsed().as_millis() as f64; 
            self.reset_topsort(elapsed_ms / (max_time_ms as f64));
            println!("Topsort reset");

            let num_edges = self.edges.iter().map(|v| v.len()).sum::<usize>();
            if num_edges == 0 {
                return Err(AnnealingError::NoEdges);
            }

            cur_eval = self.eval()?.metric;

            let mut temp = 100.;
            let mut local_max = cur_eval;
            let mut change_edge=0;
            let mut change_order = 0;
            let mut num_left = 0;
            let mut edge_or_order = 0;
            let mut old_start_vertex = 0;
            while temp >= 0.0000001 {
                if (num_left > 0 && edge_or_order == 1) || (any_partials && rng.random_range(0..2) == 0 && num_left == 0 && temp <= 0.000001) {
                    if num_left == 0 {
                        change_order = rng.random_range(0..self.orders.len());
                        if self.orders[change_order].partial == false{
                            continue;
                        }
                    }
                    let cur_order = self.orders[change_order].clone();
                    let cur_portion = cur_order.portion;
                    let mut new_portion = cur_order.portion * LogNormal::new(0.0, 1./1.5_f64.powf(20.-num_left as f64)).unwrap().sample(&mut rng);
                    if new_portion > 1.0{
                        new_portion = 1.0;
                    }
                    let buy_token_int = self.currencies_to_int[&cur_order.buy_token];
                    let sell_token_int = self.currencies_to_int[&cur_order.sell_token];
                    let default_buy_amount =  self
                    .save_orders
                    .iter()
                    .find(|o| o.id == cur_order.id)
                    .expect("Order with target_id not found")
                    .buy_amount;
                    let save_target_required = self.target_required[buy_token_int];
                    let save_target_default = self.target_default[buy_token_int];
                    let save_init = self.init[self.currencies_to_int[&cur_order.sell_token]];
                    self.target_required[buy_token_int] = self.target_required[buy_token_int].saturating_sub(U256::from_f64_lossy(cur_order.buy_amount.to_f64_lossy() * cur_portion));
                    self.target_default[buy_token_int] = self.target_default[buy_token_int].saturating_sub(U256::from_f64_lossy(default_buy_amount.to_f64_lossy() * cur_portion));
                    self.init[sell_token_int] = self.init[sell_token_int].saturating_sub(U256::from_f64_lossy(cur_order.sell_amount.to_f64_lossy() * cur_portion));
                    self.target_required[buy_token_int] += U256::from_f64_lossy(cur_order.buy_amount.to_f64_lossy() * new_portion);
                    self.target_default[buy_token_int] += U256::from_f64_lossy(default_buy_amount.to_f64_lossy() * new_portion);
                    self.init[sell_token_int] += U256::from_f64_lossy(cur_order.sell_amount.to_f64_lossy() * new_portion);
                    self.orders[change_order].portion = new_portion;
                    let delta = self.eval()?.metric - cur_eval;
                    let rand_value: f64 = rng.random::<f64>();
                    if delta > 0.0 || (rand_value < (delta / 1e36 / temp).exp() && num_left == 0) {
                        cur_eval += delta;
                    } else {
                        self.orders[change_order].portion = cur_portion;
                        self.target_required[buy_token_int] = save_target_required;
                        self.target_default[buy_token_int] = save_target_default;
                        self.init[sell_token_int] = save_init;
                    }
                    if cur_eval > local_max{
                        local_max = cur_eval;
                        edge_or_order = 1;
                        if temp < 0.001 {
                            temp = 0.001;
                        }
                        num_left = 20;
                    }

                    if cur_eval > best_eval {
                        best_eval = cur_eval;
                        best_n = self.clone();
                    }
                    temp *= 0.97;
                    if num_left > 0{
                        num_left -= 1;
                    }
                }
                // Choose random edge to modify
                change_edge = rng.random_range(0..num_edges);
                let (cur_v, cur_index) = self.find_edge_indices(change_edge);
                if num_left != 0 {
                    if old_start_vertex != cur_v{
                        continue;
                    }
                }
                let cur_edge = self.edges[cur_v][cur_index].clone();
                let edge_cur_rate = cur_edge.rate;
                
                // Modify edge rate
                let edge_new_rate;
                let mut ok = false;
                if edge_cur_rate == 0.0 {
                    if rng.random_range(0..5) != 0 {
                        continue;
                    }
                    edge_new_rate = LogNormal::new(0.0, 1.0).unwrap().sample(&mut rng);
                } else {
                    if num_left > 0 {
                        edge_new_rate = edge_cur_rate * LogNormal::new(0.0, 1./1.5_f64.powf(20.-num_left as f64)).unwrap().sample(&mut rng);
                        ok = true;
                    } else {
                        let val = rng.random_range(0..3);
                        if val == 0 {
                            edge_new_rate = 0.0;
                        } else if val == 1 {
                            edge_new_rate = LogNormal::new(0.0, 1.0).unwrap().sample(&mut rng);
                            ok = true;
                        } else {
                            edge_new_rate = edge_cur_rate * LogNormal::new(0.0, 0.1).unwrap().sample(&mut rng);
                            ok = true;
                        }
                    }
                };

                // Try new edge rate
                let mut new_edge = cur_edge.clone();
                new_edge.rate = edge_new_rate;
                self.edges[cur_v][cur_index] = new_edge;

                let delta = self.eval()?.metric - cur_eval;
                let rand_value: f64 = rng.random::<f64>();
                if delta > 0.0 || (rand_value < (delta / 1e36 / temp).exp() && num_left == 0) {
                    cur_eval += delta;
                } else {
                    self.edges[cur_v][cur_index] = cur_edge;
                }
                if cur_eval > local_max{
                    local_max = cur_eval;
                    if ok {
                        if temp < 0.001 {
                            temp = 0.001;
                        }
                        num_left = 20;
                        edge_or_order = 0;
                    }
                }

                if cur_eval > best_eval {
                    best_eval = cur_eval;
                    best_n = self.clone();
                }
                temp *= 0.97;
                old_start_vertex = cur_v;
                if num_left > 0{
                    num_left -= 1;
                }
            }
        }
        println!("The value of count is: {}", count);
        *self = best_n;
        self.eval()
    }

    fn eval(&mut self) -> Result<Evaluation, AnnealingError> {
        self.evals_called += 1;
        let mut cur_resources = self.init.clone();
        let mut num_transactions = 0;
        let mut outputs = Vec::new();

        for &i in &self.topsort {
            let sum_rate: f64 = self.edges[i].iter().map(|j| j.rate).sum();
            
            if sum_rate == 0.0 {
                continue;
            }

            if self.target_required[i] > U256::from(0) {
                if cur_resources[i] < self.target_required[i] {
                    continue;
                }
                cur_resources[i] -= self.target_required[i];
            }

            for edge in &self.edges[i] {
                if cur_resources[i] == U256::from(0) || edge.rate == 0.0 {
                    continue;
                }
                let amount_in = U256::from_f64_lossy(cur_resources[i].to_f64_lossy() * edge.rate / sum_rate);
                if amount_in == U256::from(0) {
                    continue;
                }
                let add = edge.pool.get_amount_out(
                    &self.int_to_currencies[i],
                    &self.int_to_currencies[edge.target],
                    amount_in
                );

                if add.is_err() {
                    continue;
                }

                let add = add.unwrap();

                num_transactions += 1;
                
                cur_resources[edge.target] += add;

                outputs.push(Interaction {
                    pool_id: edge.pool.get_id(),
                    in_token_id: self.int_to_currencies[i].clone(),
                    amount_in,
                    out_token_id: self.int_to_currencies[edge.target].clone(),
                    amount_out: add,
                });
            }

            cur_resources[i] = if self.target_required[i] > U256::from(0) { self.target_required[i] } else { U256::from(0) };
        }

        // Calculate metric
        let mut ans = 0.0;
        self.final_prices_map.clear();
        for i in 0..self.n {
            if self.target_required[i] != U256::from(0) {
                if cur_resources[i] >= self.target_required[i] {
                    self.final_prices_map.insert(
                        self.int_to_currencies[i].clone(),
                        self.prices[i] * self.target_required[i] / cur_resources[i]
                    );
                    ans += ((cur_resources[i] - self.target_default[i]) * self.save_prices[i]).to_f64_lossy();
                } else {
                    ans -= ((self.target_required[i] - cur_resources[i]) * self.save_prices[i] * U256::from(10000)).to_f64_lossy();
                }
            }
            if self.init[i] != U256::from(0) {
                self.final_prices_map.insert(
                    self.int_to_currencies[i].clone(),
                    self.prices[i]
                );
            }
        }

        ans -= self.fine_for_pool_usages(num_transactions);
        ans -= self.fine_for_order_usages(self.orders.len());
        let order_ids = self.orders.iter().map(|o| o.id.clone()).collect::<HashSet<_>>();

        Ok(Evaluation {
            interactions: outputs,
            metric: ans,
            orders: self.save_orders.iter().filter(|o| order_ids.contains(&o.id)).cloned().collect(),
            prices: self.final_prices_map.clone(),
        })
    }

    fn fine_for_pool_usages(&self, amount: u32) -> f64 {
        let fine_per_pool_usage = 100_000. * self.gas_price.to_f64_lossy();
        amount as f64 * 1e18 * fine_per_pool_usage
    }
    fn fine_for_order_usages(&self, amount: usize) -> f64 {
        let fine_per_pool_usage = 50_000. * self.gas_price.to_f64_lossy();
        amount as f64 * 1e18 * fine_per_pool_usage
    }
    fn find_edge_indices(&self, change_edge: usize) -> (usize, usize) {
        let x: Option<(usize, usize)> = None;
        
        let mut remaining = change_edge;
        for (i, edges) in self.edges.iter().enumerate() {
            if remaining < edges.len() {
                return (i, remaining);
            }
            remaining -= edges.len();
        }
        
        x.unwrap()
    }

    fn set_price(&mut self, token: String, price: U256) {
        self.prices_map.insert(token, price);
    }

    fn insert_pools(&mut self, pools: Vec<Pool>) {
        println!("Inserting pools");
        for pool in pools {
            let (token0, token1) = pool.get_tokens();
            self.add_edge(&token0, &token1, pool.clone());
            self.add_edge(&token1, &token0, pool.clone());
        }
        self.save_edges = self.edges.clone();
    }

    fn add_edge(&mut self, token_in: &str, token_out: &str, pool: Pool) {
        self.add_edge_with_rate(token_in, token_out, 1.0, pool);
    }

    fn add_edge_with_rate(&mut self, token_in: &str, token_out: &str, rate: f64, pool: Pool) {
        let from_idx = *self.currencies_to_int.get(token_in).unwrap_or_else(|| {
            panic!("Token {} not found", token_in);
        });
        let to_idx = *self.currencies_to_int.get(token_out).unwrap_or_else(|| {
            panic!("Token {} not found", token_out);
        });

        self.edges[from_idx].push(Edge {
            target: to_idx,
            rate,
            pool,
        });
    }

    fn set_orders(&mut self, orders: Vec<Order>) {
        self.save_orders = orders;
    }

    fn reset_topsort(&mut self, t: f64) {
        println!("Resetting topsort");
        self.edges = self.save_edges.clone();
        self.target_required = vec![U256::from(0); self.n];
        self.target_default = vec![U256::from(0); self.n];
        self.init = vec![U256::from(0); self.n];

        self.choose_orders(t);
        self.build_topsort(t);
    }

    fn choose_orders(&mut self, t: f64) {
        println!("Choosing orders");
        let mut rng = rng();
        let mut current_orders = vec![];

        // Extract all unique tokens from both sell_token and buy_token.
        let mut tokens: Vec<String> = self
            .save_orders
            .iter()
            .flat_map(|order| vec![order.sell_token.clone(), order.buy_token.clone()])
            .collect();
        tokens.sort();
        tokens.dedup();

        // Loop until at least one valid order is chosen.
        while current_orders.is_empty() {
            // Shuffle tokens randomly.
            tokens.shuffle(&mut rng);

            // Create a mapping from each token to its index in the shuffled vector.
            let token_positions: HashMap<String, usize> = tokens
                .iter()
                .enumerate()
                .map(|(i, token)| (token.clone(), i))
                .collect();

            // Iterate over save_orders and choose orders based on the initial condition
            // and the acyclic condition (sell_token must come before buy_token).
            for order in &self.save_orders {
                if t < 0.4 || rng.random_range(0..100) < 50 {
                    if token_positions[&order.sell_token] < token_positions[&order.buy_token] {
                        current_orders.push(order.clone());
                    }
                }
            }
        }

        self.orders = current_orders;
        self.set_values_for_chosen_orders();
    }

    fn set_values_for_chosen_orders(&mut self) {
    println!("set_values_for_chosen_orders");
        self.prices = vec![U256::from(0); self.n];
        
        let mut flag1 = true;
        while flag1 {
            flag1 = false;
            let mut flag2 = true;
            
            while flag2 {
                flag2 = false;
                
                for order in &self.orders {
                    let sell_idx = self.currencies_to_int[&order.sell_token];
                    let buy_idx = self.currencies_to_int[&order.buy_token];
                    let sell_amount = order.sell_amount;
                    let buy_amount = self.allowed_amounts[&order.id];
                    if self.prices[sell_idx] != U256::from(0) {
                        let limit_price = self.prices[sell_idx] * sell_amount / buy_amount;
                        if self.prices[buy_idx] == U256::from(0) || self.prices[buy_idx] > limit_price {
                            self.prices[buy_idx] = limit_price;
                            flag2 = true;
                        }
                    }
                    
                    if self.prices[buy_idx] != U256::from(0) {
                        let limit_price = self.prices[buy_idx] * buy_amount / sell_amount + U256::one();
                        if self.prices[sell_idx] == U256::from(0) || self.prices[sell_idx] < limit_price {
                            self.prices[sell_idx] = limit_price;
                            flag2 = true;
                        }
                    }
                }
            }
            
            for order in &self.orders {
                let sell_idx = self.currencies_to_int[&order.sell_token];
                if self.prices[sell_idx] == U256::from(0) {
                    self.prices[sell_idx] = self.save_prices[sell_idx];
                    flag1 = true;
                    break;
                }
            }
        }
        // Initialize target_default, update buy amounts, and set init/target values
        self.target_default = vec![U256::from(0); self.n];
        for order in &mut self.orders {
            let buy_idx = self.currencies_to_int[&order.buy_token];
            let sell_idx = self.currencies_to_int[&order.sell_token];
            
            self.target_default[buy_idx] += order.buy_amount;
            order.buy_amount = order.sell_amount * self.prices[sell_idx] / self.prices[buy_idx] + U256::one();
            self.init[sell_idx] += order.sell_amount;
            self.target_required[buy_idx] += order.buy_amount;
        }
    }

    fn build_topsort(&mut self, t: f64) {
        println!("Building topsort");
        let mut stack = VecDeque::new();
        let mut dist = vec![1e9; self.n];
        let mut num = vec![0; self.n];
        
        // Clear topsort
        self.topsort.clear();

        // Randomize edges
        for edges in &mut self.edges {
            edges.shuffle(&mut rng());
        }
        let mut order_indice = (0..self.n).collect::<Vec<_>>();
        order_indice.shuffle(&mut rng());
        // First pass: process input tokens
        for i in order_indice {
            if self.init[i] > U256::from(0) {
                stack.push_back(i);
                dist[i] = 0.;
            }
        }

        // Process stack
        while !stack.is_empty() {
            let cur_v = stack.pop_front().unwrap();
            num[cur_v] = self.topsort.len();
            self.topsort.push(cur_v);

            for edge in &self.edges[cur_v] {
                if dist[edge.target] > dist[cur_v] + 1. && self.target_required[edge.target] == U256::from(0) {
                    dist[edge.target] = dist[cur_v] + 1.;
                    stack.push_back(edge.target);
                }
            }
        }

        // Second pass: process target tokens
        order_indice = (0..self.n).collect();
        order_indice.shuffle(&mut rng());
        for i in order_indice {
            if self.target_required[i] > U256::from(0) && dist[i] == 1e9 {
                stack.push_back(i);
                dist[i] = 0.;
            }
        }

        while !stack.is_empty() {
            let cur_v = stack.pop_front().unwrap();
            if self.target_required[cur_v] > U256::from(0) {
                num[cur_v] = self.topsort.len();
                self.topsort.push(cur_v);
            }

            for edge in &self.edges[cur_v] {
                if dist[edge.target] > 1e8 && dist[edge.target] > dist[cur_v] + 1. {
                    dist[edge.target] = dist[cur_v] + 1.;
                    stack.push_back(edge.target);
                }
            }
        }

        if t > 0.8 {
            self.topsort = (0..self.n).collect();
            self.topsort.shuffle(&mut rng());
            for (i, &v) in self.topsort.iter().enumerate() {
                num[v] = i;
            }
        }

        // Filter edges based on topological order
        let mut edges2 = vec![Vec::new(); self.n];
        for i in 0..self.n {
            for edge in &self.edges[i] {
                if num[i] < num[edge.target] {
                    edges2[i].push(edge.clone());
                }
            }
        }
        self.edges = edges2;
    }
}

#[serde_as]
#[derive(Debug, Serialize, Clone)]
pub struct Interaction {
    pub pool_id: PoolId,
    pub in_token_id: String,
    #[serde_as(as = "serialize::U256")]
    pub amount_in: U256,
    pub out_token_id: String,
    #[serde_as(as = "serialize::U256")]
    pub amount_out: U256,
}