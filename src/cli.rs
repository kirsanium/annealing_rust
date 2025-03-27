use clap::Parser;
use std::path::PathBuf;

/// Command line arguments for the annealing solver
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// Path to the directory containing test inputs
    #[arg(short, long, default_value = "tests")]
    pub test_dir: PathBuf,

    /// Time limit for each simulation in milliseconds
    #[arg(short, long, default_value_t = 900)]
    pub time_limit: u64,

    /// Whether to run in verbose mode
    #[arg(short, long, default_value_t = false)]
    pub verbose: bool,
}

impl Args {
    /// Parse command line arguments
    pub fn parse() -> Self {
        Self::parse_from(std::env::args())
    }

    /// Parse command line arguments from an iterator
    pub fn parse_from<I, T>(itr: I) -> Self
    where
        I: IntoIterator<Item = T>,
        T: Into<std::ffi::OsString> + Clone,
    {
        Self::parse_from_clap(clap::Parser::parse_from(itr))
    }

    /// Parse command line arguments from clap
    pub fn parse_from_clap(args: Self) -> Self {
        args
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_args() {
        let args = Args::parse_from(["program"]);
        assert_eq!(args.test_dir.to_str().unwrap(), "tests");
        assert_eq!(args.time_limit, 900);
        assert!(!args.verbose);
    }

    #[test]
    fn test_custom_args() {
        let args = Args::parse_from([
            "program",
            "--test-dir",
            "custom_tests",
            "--time-limit",
            "1000",
            "--verbose",
        ]);
        assert_eq!(args.test_dir.to_str().unwrap(), "custom_tests");
        assert_eq!(args.time_limit, 1000);
        assert!(args.verbose);
    }
} 