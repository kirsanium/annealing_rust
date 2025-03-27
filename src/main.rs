use bigdecimal::BigDecimal;
use annealing_rust::model::TokenPair;
use annealing_rust::domain::eth::{H160, U256, H256, self};
use annealing_rust::{
    boundary::{
        self,
        baseline::{
            LiquiditySource,
            OnchainLiquidity
        }
    },
    domain::liquidity::concentrated::{
        Amount, Fee, LiquidityNet, SqrtPrice, Tick
    },
    util::conv
};
use annealing_rust::util::serialize::serialization::HexOrDecimalU256;
use annealing_rust::annealing::algorithm::*;
use serde::Serialize;
use serde_with::serde_as;
use std::fs::File;
use std::error::Error;
use std::fs;
use std::collections::HashMap;
use std::str::FromStr;
use std::sync::Arc;
use annealing_rust::cli::Args;

fn main() {
    let args = Args::parse();
    run(args.test_dir.to_str().unwrap(), args.time_limit, args.verbose).unwrap();
}

#[serde_as]
#[derive(Debug, Serialize)]
struct PathOutput {
    claimed_improvement: f64,
    success: bool,
    outputs: Vec<Interaction>,
    orders: Vec<Order>,
    #[serde_as(as = "HashMap<_, HexOrDecimalU256>")]
    prices: Prices,
}

fn get_filenames(directory_path: &str) -> Result<Vec<String>, Box<dyn Error>> {
    let path = &format!("{}/inputs/", directory_path);
    let mut filenames = Vec::new();
    for entry in fs::read_dir(path).unwrap() {
        let entry = entry.unwrap();
        let filename = entry.file_name();
        let filename_str = filename.to_string_lossy();
        if filename_str != "." && filename_str != ".." {
            filenames.push(filename_str.to_string());
        }
    }
    Ok(filenames)
}

fn create_path(
    base_dir: &str,
    num: &str,
    eval: &Evaluation,
) -> Result<(), Box<dyn Error>> {
    let path_output = PathOutput {
        claimed_improvement: eval.metric,
        success: eval.metric >= 0.0,
        outputs: eval.interactions.to_vec(),
        orders: eval.orders.to_vec(),
        prices: eval.prices.clone(),
    };

    let path = format!("{}/paths/path{}.json", base_dir, num);
    let file = File::create(path)?;
    serde_json::to_writer_pretty(file, &path_output)?;
    println!("JSON successfully written to path{}.json", num);
    Ok(())
}

fn extract_number_from_filename(filename: &str) -> String {
    filename.chars()
        .filter(|c| c.is_ascii_digit())
        .collect()
}

fn parse_prices(filename: &str) -> Result<HashMap<String, U256>, Box<dyn Error>> {
    let file = File::open(filename)?;
    let json: serde_json::Value = serde_json::from_reader(file)?;

    let mut prices = HashMap::new();
    for (token, price) in json.as_object().unwrap() {
        let price_val = parse_u256(price.as_str().unwrap());
        prices.insert(token.clone(), price_val);
    }

    Ok(prices)
}

fn parse_currencies(filename: &str) -> Result<Vec<String>, Box<dyn Error>> {
    let file = File::open(filename)?;
    let currency_addresses: Vec<String> = serde_json::from_reader(file)?;
    Ok(currency_addresses)
}

fn parse_orders(filename: &str) -> Result<Vec<Order>, Box<dyn Error>> {
    let file = File::open(filename)?;
    let orders: Vec<serde_json::Value> = serde_json::from_reader(file)?;

    let orders: Vec<_> = orders.iter().map(|order| Order {
        id: order["uid"].as_str().unwrap().to_string(),
        buy_token: order["buy_token"].as_str().unwrap().to_string(),
        sell_token: order["sell_token"].as_str().unwrap().to_string(),
        sell_amount: U256::from_f64_lossy(order["sell_amount"].as_f64().unwrap()),
        buy_amount: U256::from_f64_lossy(order["buy_amount"].as_f64().unwrap()),
    }).collect();

    Ok(orders)
}

fn parse_pools(filename: &str, currencies: &[String]) -> Result<Vec<Pool>, Box<dyn Error>> {
    let file = File::open(filename)?;
    let json: serde_json::Value = serde_json::from_reader(file)?;
    let mut used_addresses = HashMap::new();

    let mut pools = Vec::new();
    for outer_list in json.as_array().unwrap() {
        for entry in outer_list.as_array().unwrap() {
            if !entry.get("Liquidity").is_some() {
                continue;
            }

            let liquidity = &entry["Liquidity"];
            let kind = liquidity["poolType"].as_str().unwrap();
            let address = liquidity["address"].as_str().unwrap();
            let fee = liquidity["state"]["fee"].as_f64().unwrap().to_string();
            let big_dec_fee = conv::decimal_to_rational(&BigDecimal::from_str(&fee).unwrap()).unwrap();

            // Skip if address already processed
            if used_addresses.contains_key(address) {
                continue;
            }
            used_addresses.insert(address.to_string(), true);

            match kind {
                "uniswap_v3" => {
                    // Parse Uniswap V3 pool
                    let tokens = &liquidity["state"]["tokens"];
                    let token0 = tokens[0].as_str().unwrap();
                    let token1 = tokens[1].as_str().unwrap();
                    
                    let liquidity_val = u128::from_str(liquidity["state"]["liquidity"].as_str().unwrap())?;
                    let sqrt_price = parse_u256(liquidity["state"]["sqrtPrice"].as_str().unwrap());
                    let tick = liquidity["state"]["tick"].as_i64().unwrap() as i32;
                    
                    // Parse liquidity net
                    let mut liquidity_net = HashMap::new();
                    for (tick_str, liq) in liquidity["state"]["liquidityNet"].as_object().unwrap() {
                        let tick_val = tick_str.parse::<i32>()?;
                        let liq_val = liq.as_str().unwrap().parse::<i128>()?;
                        liquidity_net.insert(tick_val, liq_val);
                    }

                    pools.push(uniswap_v3_pool(address, token0, token1,
                        liquidity_val, sqrt_price, tick, &liquidity_net, big_dec_fee)?);
                },
                "uniswap_v2" => {
                    // Parse Uniswap V2 pool
                    let reserves = &liquidity["state"]["reserves"];
                    let token0 = reserves[0]["token"].as_str().unwrap();
                    let token1 = reserves[1]["token"].as_str().unwrap();

                    let reserve0 = u128::from_str(reserves[0]["amount"].as_str().unwrap())?;
                    let reserve1 = u128::from_str(reserves[1]["amount"].as_str().unwrap())?;

                    pools.push(uniswap_v2_pool(address, token0, token1, reserve0, reserve1, &fee)?);
                },
                _ => continue,
            }
        }
    }

    Ok(pools)
}

fn uniswap_v3_pool(
    address: &str,
    token_in: &str,
    token_out: &str,
    liquidity: u128,
    sqrt_price: U256,
    tick: i32,
    liquidity_net: &HashMap<i32, i128>,
    fee: eth::Rational,
) -> Result<Pool, Box<dyn Error>> {
    let pair = TokenPair::new(
        parse_h160(token_in),
        parse_h160(token_out)
    ).unwrap();

    Ok(Arc::new(OnchainLiquidity {
        id: address.to_string(),
        token_pair: pair,
        source: LiquiditySource::Concentrated(boundary::liquidity::concentrated::ConcentratedPool::new(
            eth::Address(parse_h160(address)),
            annealing_rust::domain::liquidity::TokenPair::new(
                eth::TokenAddress(parse_h160(token_in)), eth::TokenAddress(parse_h160(token_out))).unwrap(),
            SqrtPrice(sqrt_price),
            Amount(liquidity),
            Tick(tick),
            liquidity_net.clone().into_iter().map(|(k, v)| (Tick(k), LiquidityNet(v))).collect(),
            Fee(fee),
        )),
    }))
}

fn uniswap_v2_pool(
    address: &str,
    token0: &str,
    token1: &str,
    reserve0: u128,
    reserve1: u128,
    fee: &str,
) -> Result<Pool, Box<dyn Error>> {
    let pair = TokenPair::new(
        H160::from_str(&token0).unwrap(),
        H160::from_str(&token1).unwrap()
    ).unwrap();

    let fee = conv::decimal_to_rational(&BigDecimal::from_str(fee).unwrap()).unwrap();

    Ok(Arc::new(OnchainLiquidity {
        id: address.to_string(),
        token_pair: pair,
        source: LiquiditySource::ConstantProduct(boundary::liquidity::constant_product::Pool {
            address: H160::from_str(address).unwrap(),
            tokens: pair,
            reserves: (reserve0, reserve1),
            fee: num::rational::Ratio::new(fee.numer().as_u32(), fee.denom().as_u32()),
        }),
    }))
}

fn run(root_dir: &str, time_limit: u64, verbose: bool) -> Result<(), Box<dyn Error>> {
    let filenames = get_filenames(root_dir).unwrap();
    let mut success = 0;
    let mut fail = 0;
    let mut sum_good = 0.0;
    let mut goods = Vec::new();

    let prices = parse_prices(&format!("{}/normalized_prices.json", root_dir)).unwrap();

    // Process files in chunks of 3
    for file_chunk in filenames.chunks(3) {
        let num = extract_number_from_filename(&file_chunk[0]);
        
        // Parse input files
        let currencies = parse_currencies(&format!("{}/inputs/auction_{}_tokens.json", root_dir, num)).unwrap();
        let orders = parse_orders(&format!("{}/inputs/auction_{}_orders.json", root_dir, num)).unwrap();
        let pools = parse_pools(&format!("{}/inputs/auction_{}_liquidity.json", root_dir, num), &currencies).unwrap();

        let net = Net::new(prices.clone(), currencies, pools, orders);

        if let Err(e) = net {
            println!("Error: {:?}", e);
            continue;
        }

        let mut net = net.unwrap();

        // Run simulation
        let best_eval = net.run_simulation(time_limit).unwrap();

        // Update statistics
        if best_eval.metric >= 0.0 {
            success += 1;
            sum_good += best_eval.metric;
            goods.push(best_eval.metric);
        } else {
            fail += 1;
        }

        if verbose {
            println!("Processing auction {}: success={}, improvement={}", 
                num, 
                best_eval.metric >= 0.0, 
                best_eval.metric * 2750.26
            );
        }

        create_path(&root_dir, &num, &best_eval)?;
    }

    // Print final statistics
    goods.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("Results: success={}, fail={}, avg_improvement={}, median_improvement={}", 
        success, 
        fail, 
        sum_good / success as f64, 
        goods[success / 2]
    );

    if verbose {
        print!("All improvements: ");
        for good in goods {
            print!("{} ", good);
        }
        println!();
    }

    Ok(())
}

fn parse_u256(s: &str) -> U256 {
    U256::from_str_radix(s, 10).unwrap()
}

fn parse_h160(s: &str) -> H160 {
    H160::from_str(s).unwrap()
}

fn parse_h256(s: &str) -> H256 {
    H256::from_str(s).unwrap()
}