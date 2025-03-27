## Usage

The program can be run with various command-line options:

### Basic Usage
```bash
cargo run
```
This will use the default settings:
- Test directory: `tests/`
- Time limit: 900ms
- Verbose mode: disabled

### Command Line Options

```bash
cargo run -- [OPTIONS]
```

Available options:
- `--test-dir <PATH>`: Path to the directory containing test inputs (default: "tests")
- `--time-limit <MS>`: Time limit for each simulation in milliseconds (default: 900)
- `--verbose`: Enable verbose output (default: false)

### Examples

1. Run with custom test directory:
```bash
cargo run -- --test-dir /path/to/tests
```

2. Set a custom time limit:
```bash
cargo run -- --time-limit 1000
```

3. Enable verbose output:
```bash
cargo run -- --verbose
```

4. Combine options:
```bash
cargo run -- --test-dir /path/to/tests --time-limit 1000 --verbose
```

## Input Data Structure

The program expects the following directory structure:
```
tests/
├── inputs/
│   ├── auction_<N>_tokens.json
│   ├── auction_<N>_orders.json
│   └── auction_<N>_liquidity.json
├── normalized_prices.json
└── paths/
    └── path<N>.json (generated output)
```

## Output

The program generates JSON files in the `paths` directory for each processed auction, containing:
- Claimed improvement
- Success status
- Interaction outputs
- Orders
- Prices