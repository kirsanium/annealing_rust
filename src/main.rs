use bigdecimal::BigDecimal;
use annealing_rust::model::TokenPair;
use annealing_rust::domain::eth::{H160, U256, self};
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
use tycho_simulation::evm::protocol::uniswap_v4::state::{UniswapV4State, UniswapV4Fees};
use tycho_simulation::evm::protocol::utils::uniswap::tick_list::TickInfo;
use tycho_simulation::models::Token;
use tycho_simulation::protocol::models::ProtocolComponent;
use alloy::primitives::U256 as AlloyU256;
use std::fs::{File, create_dir};
use std::error::Error;
use std::fs;
use std::collections::HashMap;
use std::str::FromStr;
use std::sync::Arc;
use annealing_rust::cli::Args;
use std::path::{Path, PathBuf};

const GWEI: u128 = 1_000_000_000;

fn main() {
    println!("START");
    let args = Args::parse();
    if args.ebbo {
        run_ebbo_tests(args.test_dir.to_str().unwrap(), args.time_limit, args.threads).unwrap();
    } else {
        run(args.test_dir.to_str().unwrap(), args.time_limit, args.threads, args.verbose).unwrap();
    }
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
    let path = Path::new(directory_path).join("inputs");
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

    let path = Path::new(base_dir).join("paths");
    let _ = create_dir(path.clone());
    let path = path.join(format!("path{}.json", num));
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

fn parse_orders(filename: &str) -> Result<Vec<Order>, Box<dyn Error>> {
    let file = File::open(filename)?;
    let orders: Vec<serde_json::Value> = serde_json::from_reader(file)?;

    let orders: Vec<_> = orders.iter().map(|order| Order {
        id: order["uid"].as_str().unwrap().to_string(),
        buy_token: order["buy_token"].as_str().unwrap().to_string(),
        sell_token: order["sell_token"].as_str().unwrap().to_string(),
        sell_amount: U256::from_f64_lossy(order["sell_amount"].as_f64().unwrap()),
        buy_amount: U256::from_f64_lossy(order["buy_amount"].as_f64().unwrap()),
        partial: true,
        portion: 1.0,
    }).collect();

    Ok(orders)
}

fn parse_pools(filename: &str) -> Result<Vec<Pool>, Box<dyn Error>> {
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

fn parse_ebbo_liquidities(filename: &str) -> Result<Vec<Pool>, Box<dyn Error>> {
    let file = File::open(filename)?;
    let json: serde_json::Value = serde_json::from_reader(file)?;

    let mut pools = Vec::new();
    for pool in json.as_array().unwrap() {
        let pool_type = pool["type_pool"].as_str().unwrap();
        let pool = match pool_type {
            "uni_v3" => parse_uniswap_v3_pool_ebbo(pool),
            "uni_v4" => parse_uniswap_v4_pool_ebbo(pool),
            _ => {
                println!("Unknown pool type: {}", pool_type);
                continue;
            },
        };
        match pool {
            Ok(pool) => pools.push(pool),
            Err(e) => {
                println!("Error parsing pool: {:?}", e);
                continue;
            },
        };
    }

    Ok(pools)
}

fn parse_uniswap_v3_pool_ebbo(pool: &serde_json::Value) -> Result<Pool, Box<dyn Error>> {
    let address = pool["address"].as_str().unwrap();
    let tokens = pool["token_pair"].as_str().unwrap();
    let tokens: Vec<&str> = tokens[1..tokens.len()-1].split(",").map(|s| s.trim()).collect::<Vec<&str>>();

    let liquidity = u128::from_str(pool["liquidity"].as_str().unwrap())?;
    let sqrt_price = U256::from_str_radix(pool["sqrt_price"].as_str().unwrap(), 10).unwrap();
    let tick = i32::from_str(pool["tick"].as_str().unwrap())?;
    let liquidity_net = pool["ticks"].as_array().unwrap().iter().map(|tick| {
        let index = tick["index"].as_i64().unwrap();
        let liquidity = i128::from_str(tick["net_liquidity"].as_str().unwrap()).unwrap();
        (index as i32, liquidity)
    }).collect::<HashMap<i32, i128>>();
    let fee = eth::Rational::new_raw(
        pool["fee"]["numer"].as_u64().unwrap().into(),
        pool["fee"]["denom"].as_u64().unwrap().into()
    );

    uniswap_v3_pool(
        address, 
        tokens[0], 
        tokens[1], 
        liquidity, 
        sqrt_price, 
        tick, 
        &liquidity_net,
        fee
    )
}

fn parse_uniswap_v4_pool_ebbo(pool: &serde_json::Value) -> Result<Pool, Box<dyn Error>> {
    let address = pool["address"].as_str().unwrap();
    let tokens = pool["token_pair"].as_str().unwrap();
    let tokens = tokens[1..tokens.len()-1].split(",").map(|s| s.trim()).collect::<Vec<&str>>();
    let liquidity = u128::from_str(pool["other_params"]["liquidity"].as_str().unwrap())?;
    let sqrt_price = string_to_alloy_u256(pool["other_params"]["sqrt_price"].as_str().unwrap());
    let tick = pool["other_params"]["tick"].as_i64().unwrap() as i32;
    let tick_spacing = pool["other_params"]["tick_spacing"].as_i64().unwrap() as i32;
    let fees = UniswapV4Fees::new(
        pool["other_params"]["fees"]["zero_for_one"].as_u64().unwrap() as u32,
        pool["other_params"]["fees"]["one_for_zero"].as_u64().unwrap() as u32,
        pool["other_params"]["fees"]["lp_fee"].as_u64().unwrap() as u32,
    );
    let ticks = pool["ticks"].as_array().unwrap().iter().map(|tick| {
        let index = tick["index"].as_i64().unwrap() as i32;
        let liquidity = tick["net_liquidity"].as_str().unwrap().parse::<i128>().unwrap();
        TickInfo::new(index, liquidity)
    }).collect();

    uniswap_v4_pool(
        address,
        tokens,
        liquidity,
        sqrt_price,
        tick,
        tick_spacing,
        ticks,
        fees
    )
}

fn uniswap_v4_pool(
    address: &str,
    tokens: Vec<&str>,
    liquidity: u128,
    sqrt_price: AlloyU256,
    tick: i32,
    tick_spacing: i32,
    ticks: Vec<TickInfo>,
    fees: UniswapV4Fees,
) -> Result<Pool, Box<dyn Error>> {
    let pair = TokenPair::new(
        parse_h160(tokens[0]),
        parse_h160(tokens[1])
    ).unwrap();

    Ok(Arc::new(OnchainLiquidity {
        id: address.to_string(),
        token_pair: pair,
        source: LiquiditySource::Tycho(boundary::liquidity::tycho::TychoPool::new(
            ProtocolComponent::new(
                hex::decode(&address[2..]).unwrap().into(),
                "uniswap_v4".to_string(),
                "uniswap_v4_pool".to_string(),
                Default::default(),
                tokens.into_iter().map(|token| Token::new(
                    token,
                    Default::default(),
                    Default::default(),
                    Default::default()
                )).collect(),
                Default::default(),
                Default::default(),
                Default::default(),
                Default::default()
            ),
            Arc::new(UniswapV4State::new(
                liquidity,
                sqrt_price,
                fees,
                tick,
                tick_spacing,
                ticks,
            ))
        )),
    }))
}

fn string_to_alloy_u256(value: &str) -> AlloyU256 {
    let mut array = [0u8; 32];
    U256::from_str_radix(value, 10).unwrap().to_big_endian(&mut array);
    AlloyU256::from_be_bytes(array)
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

fn run(root_dir: &str, time_limit: u64, threads: usize, verbose: bool) -> Result<(), Box<dyn Error>> {
    // Create paths directory if it doesn't exist
    let paths_dir = Path::new(root_dir).join("paths");
    fs::create_dir_all(&paths_dir)?;
    let filenames = get_filenames(root_dir).unwrap();
    let mut success = 0;
    let mut fail = 0;
    let mut sum_good = 0.0;
    let mut goods = Vec::new();

    let prices = parse_prices(&Path::new(root_dir).join("normalized_prices.json").to_string_lossy())?;
    // Process files in chunks of 3
    for file_chunk in filenames.chunks(3) {
        let num = extract_number_from_filename(&file_chunk[0]);
        
        // Parse input files
        let orders = parse_orders(&Path::new(root_dir).join("inputs").join(format!("auction_{}_orders.json", num)).to_string_lossy())?;
        let pools = parse_pools(&Path::new(root_dir).join("inputs").join(format!("auction_{}_liquidity.json", num)).to_string_lossy())?;
        
        let eval = Annealing::run(threads, time_limit, AnnealingArgs {
            prices: prices.clone(),
            pools: pools.clone(),
            orders: orders.clone(),
            gas_price: U256::from(3*GWEI),
        });

        if let Err(e) = eval {
            println!("Error: {:?}", e);
            fail += 1;
            continue;
        }

        let eval = eval.unwrap();

        // Update statistics
        if eval.metric >= 0.0 {
            success += 1;
            sum_good += eval.metric;
            goods.push(eval.metric);
        } else {
            fail += 1;
        }

        if verbose {
            println!("Processing auction {}: success={}, improvement={}", 
                num, 
                eval.metric >= 0.0, 
                eval.metric * 2750.26
            );
        }

        create_path(root_dir, &num, &eval)?;
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

fn run_ebbo_tests(root_dir: &str, time_limit: u64, threads: usize) -> Result<(), Box<dyn Error>> {
    let ebbo_path = Path::new(root_dir).join("ebbo");
    let ebbo_pools = parse_ebbo_liquidities(&ebbo_path.join("ebbo_pools.json").to_string_lossy())?;
    let ebbo_orders = parse_orders(&ebbo_path.join("ebbo_orders.json").to_string_lossy())?;
    let ebbo_prices = parse_prices(&ebbo_path.join("ebbo_prices.json").to_string_lossy())?;
    let eval = Annealing::run(threads, time_limit, AnnealingArgs {
        prices: ebbo_prices,
        pools: ebbo_pools,
        orders: ebbo_orders,
        gas_price: U256::from(3*GWEI),
    }).unwrap();

    create_path(root_dir, "ebbo", &eval)?;

    Ok(())
}

fn parse_u256(s: &str) -> U256 {
    U256::from_str_radix(s, 10).unwrap()
}

fn parse_h160(s: &str) -> H160 {
    H160::from_str(s).unwrap()
}