use {
    crate::domain::{eth::{self, U256}, liquidity},
    ethereum_types::H160,
    std::collections::BTreeMap,
};
use crate::baseline_solver::{BaselineSolvable, BaselineSolverError};
use crate::domain::liquidity::concentrated::{Amount, Fee, LiquidityNet, SqrtPrice, Tick};

#[derive(Clone, Debug)]
pub struct ConcentratedPool {
    pub address: eth::Address,
    pub tokens: liquidity::TokenPair,
    pub sqrt_price: SqrtPrice,
    pub liquidity: Amount,
    pub tick: Tick,
    pub liquidity_net: BTreeMap<Tick, LiquidityNet>,
    pub fee: Fee,
    tycho_pool: tycho_maths::TychoUniswapV3State,
}

/// Converts a domain pool into a [`shared`] Uniswap v3 concentrated pool. Returns
/// `None` if the domain pool cannot be represented as a boundary pool.
pub fn to_boundary_pool(address: H160, pool: &liquidity::concentrated::Pool) -> ConcentratedPool {
    ConcentratedPool::new(
        eth::Address(address),
        pool.tokens,
        pool.sqrt_price,
        pool.liquidity,
        pool.tick,
        pool.liquidity_net.clone(),
        pool.fee.clone(),
    )
}

pub const CONCENTRATED_SWAP_GAS_COST: usize = 108163;

mod tycho_maths {
    use lazy_static::lazy_static;
    use crate::domain::liquidity::concentrated::Fee;
    use tycho_simulation::evm::protocol::utils::uniswap::tick_list::TickInfo;
    use tycho_simulation::protocol::state::ProtocolSim;
    use num_bigint::BigUint;
    use ethcontract::{U256, H160};
    use tycho_simulation::models::Token;
    use crate::util::conv;
    use tycho_simulation::protocol::errors::SimulationError;
    use super::{Amount, SqrtPrice, Tick, LiquidityNet, BTreeMap};

    type TychoFee = tycho_simulation::evm::protocol::uniswap_v3::enums::FeeAmount;
    pub(crate) type TychoUniswapV3State = tycho_simulation::evm::protocol::uniswap_v3::state::UniswapV3State;
    pub(crate) type TychoUniswapV4State = tycho_simulation::evm::protocol::uniswap_v4::state::UniswapV4State;

    lazy_static! {
        static ref LOWEST_FEE: Fee = Fee(conv::decimal_to_rational(&"0.0001".parse().unwrap()).unwrap());
        static ref LOW_FEE: Fee = Fee(conv::decimal_to_rational(&"0.0005".parse().unwrap()).unwrap());
        static ref MEDIUM_LOW_FEE: Fee = Fee(conv::decimal_to_rational(&"0.0025".parse().unwrap()).unwrap());
        static ref MEDIUM_FEE: Fee = Fee(conv::decimal_to_rational(&"0.003".parse().unwrap()).unwrap());
        static ref MEDIUM_HIGH_FEE: Fee = Fee(conv::decimal_to_rational(&"0.005".parse().unwrap()).unwrap());
        static ref HIGH_FEE: Fee = Fee(conv::decimal_to_rational(&"0.01".parse().unwrap()).unwrap());
    }

    fn fees_equal(fee1: &Fee, fee2: &Fee) -> bool {
        fee1.0.numer().checked_mul(*fee2.0.denom()).unwrap() == fee1.0.denom().checked_mul(*fee2.0.numer()).unwrap()
    }

    pub struct AlloyU256(alloy::primitives::U256);

    impl From<U256> for AlloyU256 {
        fn from(value: U256) -> Self {
            let mut bytes = [0u8; 32];
            let le_amount = bytes.as_mut_slice();
            value.to_little_endian(le_amount);
            AlloyU256(alloy::primitives::U256::from_le_slice(le_amount))
        }
    }

    impl From<AlloyU256> for alloy::primitives::U256 {
        fn from(value: AlloyU256) -> Self {
            value.0
        }
    }

    impl From<Fee> for TychoFee {
        fn from(value: Fee) -> Self {
            if fees_equal(&value, &LOWEST_FEE) {
                TychoFee::Lowest
            } else if fees_equal(&value, &LOW_FEE) {
                TychoFee::Low
            } else if fees_equal(&value, &MEDIUM_LOW_FEE) {
                TychoFee::MediumLow
            } else if fees_equal(&value, &MEDIUM_FEE) {
                TychoFee::Medium
            } else if fees_equal(&value, &MEDIUM_HIGH_FEE) {
                TychoFee::MediumHigh
            } else if fees_equal(&value, &HIGH_FEE) {
                TychoFee::High
            } else {
                panic!("Unsupported fee: {:?}", value)
            }
        }
    }

    pub(super)fn u256_to_biguint(value: U256) -> BigUint {
        let mut bytes = [0u8; 32];
        let le_amount = bytes.as_mut_slice();
        value.to_little_endian(le_amount);
        BigUint::from_bytes_le(le_amount)
    }

    pub(super)fn biguint_to_u256(value: BigUint) -> U256 {
        let bytes = value.to_bytes_le();
        U256::from_little_endian(&bytes)
    }

    // this is a hack: we initalize tycho token with address only,
    // to use tycho's uniswap_v3 maths implementation,
    // because only address is used in calculations
    fn h160_to_token(value: H160) -> Token {
        Token::new(hex::encode(value.0).as_str(), 18, "ETH", BigUint::from(0u64))
    }

    pub enum TychoMathsError {
        SimulationError(String),
    }

    impl From<SimulationError> for TychoMathsError {
        fn from(error: SimulationError) -> Self {
            TychoMathsError::SimulationError(error.to_string())
        }
    }

    pub fn build_tycho_pool(
        liquidity: Amount,
        sqrt_price: SqrtPrice,
        fee: Fee,
        tick: Tick,
        liquidity_net: &BTreeMap<Tick, LiquidityNet>,
    ) -> TychoUniswapV3State {
        TychoUniswapV3State::new(
            liquidity.0,
            AlloyU256::from(sqrt_price.0).into(),
            fee.into(),
            tick.0,
            liquidity_net.iter().map(|(tick, liquidity_net)| 
                TickInfo::new(tick.0, liquidity_net.0)).collect(),
        )
    }

    pub fn get_amount_out(pool: &super::ConcentratedPool, out_token: H160, input: (U256, H160)) -> Result<U256, TychoMathsError> {
        let result = pool.tycho_pool.get_amount_out(
            u256_to_biguint(input.0),
            &h160_to_token(input.1),
            &h160_to_token(out_token)
        )?;

        Ok(biguint_to_u256(result.amount))
    }
}

impl From<tycho_maths::TychoMathsError> for BaselineSolverError {
    fn from(error: tycho_maths::TychoMathsError) -> Self {
        match error {
            tycho_maths::TychoMathsError::SimulationError(msg) => BaselineSolverError::AmountCalculation(msg),
        }
    }
}

impl BaselineSolvable for ConcentratedPool {
    fn get_amount_out(&self, out_token: H160, input: (U256, H160)) -> Result<U256, BaselineSolverError> {
        let token_pair = liquidity::TokenPair::new(input.1.into(), out_token.into());
        match token_pair {
            None => {
                let msg = format!("Invalid token pair: {:?}", self.tokens);
                return Err(BaselineSolverError::InvalidToken(msg));
            },
            Some(pair) => {
                if pair != self.tokens {
                    let msg = format!("Invalid token pair: {:?} != {:?}", pair, self.tokens);
                    return Err(BaselineSolverError::InvalidToken(msg));
                }
            }
        }

        Ok(tycho_maths::get_amount_out(self, out_token, input)?)
    }


    fn get_amount_in(&self, in_token: H160, output: (U256, H160)) -> Result<U256, BaselineSolverError> {
        let right0 = self.get_right_border(in_token, output)
            .ok_or(BaselineSolverError::AmountCalculation("Right border not found".into()))?;
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

    fn get_approx_amount_out(&self, _out_token: H160, input: (U256, H160)) -> Result<U256, BaselineSolverError> {
        let is_token_in_equals_token0 = input.1 == self.tokens.get().0.0;
        let coeff = self.approx_coefficient(is_token_in_equals_token0);
        Ok(U256::from_f64_lossy(input.0.to_f64_lossy() * coeff))
    }

    fn get_approx_amount_in(&self, in_token: H160, out: (U256, H160)) -> Result<U256, BaselineSolverError> {
        let is_token_in_equals_token0 = in_token == self.tokens.get().0.0;
        let coeff = self.approx_coefficient(is_token_in_equals_token0);
        Ok(U256::from_f64_lossy(out.0.to_f64_lossy() / coeff))
    }

    fn gas_cost(&self) -> usize {
        CONCENTRATED_SWAP_GAS_COST
    }
}

impl ConcentratedPool {
    /// Creates a new ConcentratedPool instance
    pub fn new(
        address: eth::Address,
        tokens: liquidity::TokenPair,
        sqrt_price: SqrtPrice,
        liquidity: Amount,
        tick: Tick,
        liquidity_net: BTreeMap<Tick, LiquidityNet>,
        fee: Fee,
    ) -> Self {
        let tycho_pool = tycho_maths::build_tycho_pool(
            liquidity,
            sqrt_price,
            fee.clone(),
            tick,
            &liquidity_net,
        );
        Self {
            address,
            tokens,
            sqrt_price,
            liquidity,
            tick,
            liquidity_net,
            fee,
            tycho_pool,
        }
    }

    fn sqrt_price_f64(&self) -> f64 {
        self.sqrt_price.0.to_f64_lossy() / 2_f64.powf(96_f64)
    }

    fn fee_f64(&self) -> f64 {
        self.fee.0.numer().to_f64_lossy() / self.fee.0.denom().to_f64_lossy()
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

    fn approx_coefficient(&self, is_r0_equals_token0: bool) -> f64 {
        let sqrt_p = self.sqrt_price_f64();
        let fee = self.fee_f64();
        if !is_r0_equals_token0 {
            sqrt_p.powf(-2_f64) * (1_f64 - fee / 1000000_f64)
        } else {
            sqrt_p.powf(2_f64) * (1_f64 - fee / 1000000_f64)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;
    use bigdecimal::BigDecimal;
    use crate::domain::eth::TokenAddress;
    use crate::domain::liquidity::TokenPair;
    use crate::util::conv;
    use super::*;
    use num_bigint::BigUint;
    use super::tycho_maths::{biguint_to_u256, u256_to_biguint};

    fn pool_unsorted() -> ConcentratedPool {
        let liquidity_net = vec![
            ("-276334", "84829712324032664595"),
            ("887272", "-2012332486698"),
            ("-276338", "1129201697274567052601"),
            ("-276335", "198294687896206754182"),
            ("-276329", "386295756000803"),
            ("-276344", "99170541131100"),
            ("-276324", "68719476736"),
            ("-276327", "34059840767224416399"),
            ("-276326", "269300482105873772"),
            ("-276347", "52398940099379429634"),
            ("-276323", "-1697540987048434"),
            ("-276337", "886873759007655653374"),
            ("-276315", "-282774589451039374513"),
            ("-276322", "12919576657070817"),
            ("-276317", "-897316478405405933637"),
            ("-276330", "43971541471533855"),
            ("-276316", "-206554461869720836889"),
            ("-276308", "-240733239871420168"),
            ("-276307", "-52398940099379429634"),
            ("-276306", "-192836083098624304"),
            ("-276319", "165061562307270970"),
            ("-276304", "-99170541131100"),
            ("-276295", "-1"),
            ("-276332", "39803680324170563"),
            ("-276325", "9152151336529588"),
            ("-276321", "-24233082746359161"),
            ("-276320", "-207063683879008756758"),
            ("-276296", "1"),
            ("-276328", "202773562055813311"),
            ("-276302", "-49136238908544129"),
            ("-276342", "49136238908544129"),
            ("-276313", "-434099576578084216"),
            ("-276305", "-1949943270408685"),
            ("-276340", "398633310109411"),
            ("-276331", "10824695179444004"),
            ("-276343", "152376927527190466261"),
            ("-276311", "-10824695179444004"),
            ("-276333", "183332701092815099026"),
            ("-276301", "-204291277875907"),
            ("-887272", "2012332486698"),
            ("-276336", "454210104283867705"),
            ("-276312", "-35364780001147975"),
            ("-276310", "-43971541471533855"),
            ("-276314", "-1075482999863542419467")
        ];
        let liquidity_net: BTreeMap<Tick, LiquidityNet> = liquidity_net.into_iter()
            .map(|(tick, l)|
            (
                Tick(tick.parse().unwrap()),
                LiquidityNet(l.parse().unwrap())
            ))
            .collect();
        ConcentratedPool::new(
            Default::default(),
            // [DAI(18), USDT(6)]
            // ["0x6b175474e89094c44da98b954eedeac495271d0f","0xdac17f958d2ee523a2206206994597c13d831ec7"]
            TokenPair::new(TokenAddress(H160::zero()), TokenAddress(H160::from_low_u64_be(1))).unwrap(),
            SqrtPrice(U256::from_str_radix("79211568900943603601687", 10).unwrap()),
            Amount(2687907257593954407941),
            Tick(-276329),
            liquidity_net,
            Fee(conv::decimal_to_rational(&BigDecimal::from_str("0.0001").unwrap()).unwrap()),
        )
    }

    #[test]
    fn dai_usdt_sell() {
        let pool = pool_unsorted();
        let amount_out = pool.get_amount_out(
            H160::from_low_u64_be(1),
            (U256::exp10(18), H160::zero())
        ).unwrap();

        assert_eq!(U256::from_str_radix("999481", 10).unwrap(), amount_out)
    }

    #[test]
    fn dai_usdt_buy() {
        let pool = pool_unsorted();
        let amount_in = pool.get_amount_in(
            H160::zero(),
            (U256::from_str_radix("999481", 10).unwrap(), H160::from_low_u64_be(1))
        ).unwrap();

        assert_eq!(U256::from_str_radix("1000003799018658555", 10).unwrap(), amount_in)
    }

    #[test]
    fn usdt_dai_sell() {
        let pool = pool_unsorted();
        let amount_out = pool.get_amount_out(
            H160::zero(),
            (U256::from_str_radix("999683", 10).unwrap(), H160::from_low_u64_be(1))
        ).unwrap();

        assert_eq!(U256::from_str_radix("1000001838223019296", 10).unwrap(), amount_out)
    }

    #[test]
    #[should_panic]
    fn usdt_dai_buy_too_much() {
        let pool = pool_unsorted();
        let amount_out = pool.get_amount_in(
            H160::from_low_u64_be(1),
            (U256::exp10(24)*2, H160::zero())
        ).unwrap();
    
        assert_eq!(U256::from_str_radix("2000000000000", 10).unwrap(), amount_out)
    }

    #[test]
    fn usdt_dai_buy() {
        let pool = pool_unsorted();
        let amount_out = pool.get_amount_in(
            H160::from_low_u64_be(1),
            (U256::exp10(18), H160::zero())
        ).unwrap();
    
        assert_eq!(U256::from_str_radix("999683", 10).unwrap(), amount_out)
    }

    fn build_liquidity_net(liquidity_net: Vec<(&str, &str)>) -> BTreeMap<Tick, LiquidityNet> {
        liquidity_net.into_iter().fold(BTreeMap::new(),
           |mut acc, entry| {
               acc.insert(Tick(entry.0.parse().unwrap()), LiquidityNet(entry.1.parse().unwrap()));
               acc
           })
    }

    fn pool() -> ConcentratedPool {
        let liquidity_net = vec![
            ("-887272", "509985308420834"),
            ("-207245", "861372880833280"),
            ("-205412", "870583342667379"),
            ("-205286", "62243380720423"),
            ("-205279", "7754484356792"),
            ("-205270", "-7754484356792"),
            ("-205266", "-62243380720423"),
            ("-200412", "38922731378986"),
            ("-199895", "-38922731378986"),
            ("-199588", "884924438687748"),
            ("-199359", "356531808516887"),
            ("-199358", "151657111769369"),
            ("-198914", "-884924438687748"),
            ("-198848", "69231152773837"),
            ("-198829", "-69231152773837"),
            ("-198533", "78195380914566"),
            ("-198080", "725236835072227"),
            ("-197421", "792163544307120"),
            ("-197384", "6573447416137938"),
            ("-197328", "3602665832241317"),
            ("-197309", "-151657111769369"),
            ("-197127", "371549156461246"),
            ("-197054", "4713588722987450"),
            ("-196947", "4283124027918463"),
            ("-196840", "555197705808149"),
            ("-196707", "55040828865502"),
            ("-196682", "106925946128513"),
            ("-196596", "172024463955746"),
            ("-196595", "66249539495303483"),
            ("-196565", "513761754781922"),
            ("-196425", "1602709602804441"),
            ("-196357", "24448431016597321"),
            ("-196224", "81666963360569358"),
            ("-196094", "-78195380914566"),
            ("-196059", "-24448431016597321"),
            ("-196026", "520202268528394"),
            ("-195833", "729663811259263"),
            ("-195666", "-106925946128513"),
            ("-195611", "-371549156461246"),
            ("-195394", "-4713588722987450"),
            ("-195305", "-3874609458541723"),
            ("-195304", "15482287763383219"),
            ("-195172", "-513761754781922"),
            ("-195005", "85768468508830058"),
            ("-194714", "-792163544307120"),
            ("-194700", "-55040828865502"),
            ("-194600", "-6573447416137938"),
            ("-194571", "-3602665832241317"),
            ("-194489", "8017267496262492"),
            ("-194186", "-16037485469191368"),
            ("-194138", "-86288670777358452"),
            ("-194079", "-8017267496262492"),
            ("-194025", "-729663811259263"),
            ("-194021", "-870583342667379"),
            ("-193893", "-408514569376740"),
            ("-193633", "-66249539495303483"),
            ("-193380", "-172024463955746"),
            ("-192892", "-83269672963373799"),
            ("-191148", "-725236835072227"),
            ("-185270", "-861372880833280"),
            ("-183263", "-356531808516887"),
            ("887272", "-509985308420834"),
        ];
        let liquidity_net = build_liquidity_net(liquidity_net);
        ConcentratedPool::new(
            Default::default(),
            TokenPair::new(TokenAddress(H160::zero()), TokenAddress(H160::from_low_u64_be(1))).unwrap(),
            SqrtPrice(U256::from_str_radix("4806566537446624286014559", 10).unwrap()),
            Amount(264496549221591950),
            Tick(-194212),
            liquidity_net,
            Fee(conv::decimal_to_rational(&BigDecimal::from_str("0.0001").unwrap()).unwrap()),
        )
    }

    #[test]
    fn weth_usd_sell() {
        let pool = pool();
        let amount_out = pool.get_amount_out(
            H160::from_low_u64_be(1),
            (U256::exp10(18), H160::zero())
        ).unwrap();

        assert_eq!(U256::from_str_radix("3679321393", 10).unwrap(), amount_out)
    }

    #[test]
    fn approx_weth_usd_sell() {
        let pool = pool();
        let amount_out = pool.get_approx_amount_out(
            H160::from_low_u64_be(1),
            (U256::exp10(18), H160::zero())
        ).unwrap();

        // 3680533285 is a little bit more than 3679321393 from the last test
        assert_eq!(U256::from_str_radix("3680533285", 10).unwrap(), amount_out)
    }

    #[test]
    fn weth_usd_buy() {
        let pool = pool();
        let amount_in = pool.get_amount_in(
            H160::zero(),
            (U256::from_str_radix("3679321393", 10).unwrap(), H160::from_low_u64_be(1))
        ).unwrap();

        assert_eq!(U256::from_str_radix("1000003055862008096", 10).unwrap(), amount_in)
    }

    #[test]
    fn approx_weth_usd_buy() {
        let pool = pool();
        let amount_in = pool.get_approx_amount_in(
            H160::zero(),
            (U256::from_str_radix("3679321393", 10).unwrap(), H160::from_low_u64_be(1))
        ).unwrap();

        assert_eq!(U256::from_str_radix("999670728970865536", 10).unwrap(), amount_in)
    }

    #[test]
    fn usd_weth_sell() {
        let pool = pool();
        let amount_out = pool.get_amount_out(
            H160::zero(),
            (U256::from_str_radix("3600000000", 10).unwrap(), H160::from_low_u64_be(1))
        ).unwrap();

        assert_eq!(U256::from_str_radix("977801965285213557", 10).unwrap(), amount_out)
    }

    #[test]
    fn approx_usd_weth_sell() {
        let pool = pool();
        let amount_out = pool.get_approx_amount_out(
            H160::zero(),
            (U256::from_str_radix("3600000000", 10).unwrap(), H160::from_low_u64_be(1))
        ).unwrap();

        assert_eq!(U256::from_str_radix("978119125559997696", 10).unwrap(), amount_out)
    }

    #[test]
    fn usd_weth_buy() {
        let pool = pool();
        let amount_out = pool.get_amount_in(
            H160::from_low_u64_be(1),
            (U256::from_str_radix("977801965285031552", 10).unwrap(), H160::zero())
        ).unwrap();

        assert_eq!(U256::from_str_radix("3600012804", 10).unwrap(), amount_out)
    }

    #[test]
    fn approx_usd_weth_buy() {
        let pool = pool();
        let amount_out = pool.get_approx_amount_in(
            H160::from_low_u64_be(1),
            (U256::from_str_radix("977801965285031552", 10).unwrap(), H160::zero())
        ).unwrap();

        assert_eq!(U256::from_str_radix("3598832681", 10).unwrap(), amount_out)
    }

    #[test]
    fn test_get_amount_out_full_range_liquidity() {
        let token_x = H160::from_str("0x6b175474e89094c44da98b954eedeac495271d0f").unwrap();
        let token_y = H160::from_str("0xf1ca9cb74685755965c7458528a36934df52a3ef").unwrap();

        let pool = ConcentratedPool::new(
            Default::default(),
            TokenPair::new(TokenAddress(token_x), TokenAddress(token_y)).unwrap(),
            SqrtPrice(U256::from_str_radix("188562464004052255423565206602", 10).unwrap()),
            Amount(8330443394424070888454257),
            Tick(17342),
            build_liquidity_net(vec![
                ("0", "0"),
                ("46080", "0"),
            ]),
            Fee(conv::decimal_to_rational(&BigDecimal::from_str("0.003").unwrap()).unwrap()),
        );

        let sell_amount = U256::from_str_radix("11000000000000000000000", 10).unwrap();
        let expected = U256::from_str_radix("61927070842678722935941", 10).unwrap();

        let res = pool
            .get_amount_out(token_y, (sell_amount, token_x))
            .unwrap();

        assert_eq!(res, expected);
    }

    struct SwapTestCase {
        symbol: &'static str,
        sell: U256,
        exp: U256,
    }

    #[test]
    fn test_get_amount_out() {
        let wbtc = H160::from_str("0x2260FAC5E5542a773Aa44fBCfeDf7C193bc2C599").unwrap();
        let weth = H160::from_str("0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2").unwrap();
        let pool = ConcentratedPool::new(
            Default::default(),
            TokenPair::new(TokenAddress(wbtc), TokenAddress(weth)).unwrap(),
            SqrtPrice(U256::from_str_radix("28437325270877025820973479874632004", 10).unwrap()),
            Amount(377952820878029838),
            Tick(255830),
            build_liquidity_net(vec![
                ("255760", "1759015528199933"),
                ("255770", "6393138051835308"),
                ("255780", "228206673808681"),
                ("255820", "1319490609195820"),
                ("255830", "678916926147901"),
                ("255840", "12208947683433103"),
                ("255850", "1177970713095301"),
                ("255860", "8752304680520407"),
                ("255880", "1486478248067104"),
                ("255890", "1878744276123248"),
                ("255900", "77340284046725227"),
            ]),
            Fee(conv::decimal_to_rational(&BigDecimal::from_str("0.0005").unwrap()).unwrap()),
        );
        let cases = vec![
            SwapTestCase {
                symbol: "WBTC",
                sell: U256::from_str_radix("500000000", 10).unwrap(),
                exp: U256::from_str_radix("64352395915550406461", 10).unwrap(),
            },
            SwapTestCase {
                symbol: "WBTC",
                sell: U256::from_str_radix("550000000", 10).unwrap(),
                exp: U256::from_str_radix("70784271504035662865", 10).unwrap(),
            },
            SwapTestCase {
                symbol: "WBTC",
                sell: U256::from_str_radix("600000000", 10).unwrap(),
                exp: U256::from_str_radix("77215534856185613494", 10).unwrap(),
            },
            SwapTestCase {
                symbol: "WBTC",
                sell: U256::from_str_radix("1000000000", 10).unwrap(),
                exp: U256::from_str_radix("128643569649663616249", 10).unwrap(),
            },
            SwapTestCase {
                symbol: "WBTC",
                sell: U256::from_str_radix("3000000000", 10).unwrap(),
                exp: U256::from_str_radix("385196519076234662939", 10).unwrap(),
            },
            SwapTestCase {
                symbol: "WETH",
                sell: U256::from_str_radix("64000000000000000000", 10).unwrap(),
                exp: U256::from_str_radix("496294784", 10).unwrap(),
            },
            SwapTestCase {
                symbol: "WETH",
                sell: U256::from_str_radix("70000000000000000000", 10).unwrap(),
                exp: U256::from_str_radix("542798479", 10).unwrap(),
            },
            SwapTestCase {
                symbol: "WETH",
                sell: U256::from_str_radix("77000000000000000000", 10).unwrap(),
                exp: U256::from_str_radix("597047757", 10).unwrap(),
            },
            SwapTestCase {
                symbol: "WETH",
                sell: U256::from_str_radix("128000000000000000000", 10).unwrap(),
                exp: U256::from_str_radix("992129037", 10).unwrap(),
            },
            SwapTestCase {
                symbol: "WETH",
                sell: U256::from_str_radix("385000000000000000000", 10).unwrap(),
                exp: U256::from_str_radix("2978713582", 10).unwrap(),
            },
        ];

        for case in cases {
            let (token_a, token_b) =
                if case.symbol == "WBTC" { (&wbtc, &weth) } else { (&weth, &wbtc) };
            let res = pool
                .get_amount_out(*token_b, (case.sell, *token_a))
                .unwrap();

            assert_eq!(res, case.exp);
        }
    }

    #[test]
    fn test_u256_biguint_conversions() {
        // Test small numbers
        let small_u256 = U256::from(42);
        let small_biguint = u256_to_biguint(small_u256);
        assert_eq!(small_biguint, BigUint::from(42u64));
        assert_eq!(biguint_to_u256(small_biguint), small_u256);

        // Test large numbers
        let large_u256 = U256::from_dec_str("115792089237316195423570985008687907853269984665640564039457584007913129639935").unwrap();
        let large_biguint = BigUint::from_str("115792089237316195423570985008687907853269984665640564039457584007913129639935").unwrap();
        assert_eq!(biguint_to_u256(large_biguint), large_u256);

        // Test zero
        let zero_u256 = U256::zero();
        let zero_biguint = u256_to_biguint(zero_u256);
        assert_eq!(zero_biguint, BigUint::from(0u64));
        assert_eq!(biguint_to_u256(zero_biguint), zero_u256);

        // Test powers of 2
        let pow2_u256 = U256::from(1) << 255;
        let pow2_biguint = u256_to_biguint(pow2_u256);
        assert_eq!(biguint_to_u256(pow2_biguint), pow2_u256);
    }
}
