use clap::*;
use serde::{Deserialize, Serialize};

#[derive(Parser, Serialize, Deserialize)]
pub struct RocqOfRustArgs {
    /// Axiomatize the definitions
    #[arg(long)]
    axiomatize: bool,
    /// Also generate a JSON output
    #[arg(long)]
    with_json: bool,
    /// Deprecated compatibility option (ignored)
    #[arg(long)]
    configuration_file: Option<String>,
    /// Deprecated compatibility option (ignored)
    #[arg(long)]
    generate_reorder: bool,
}

impl RocqOfRustArgs {
    pub fn warn_deprecated(&self) {
        if self.configuration_file.is_some() {
            eprintln!("warning: --configuration-file is deprecated and ignored");
        }
        if self.generate_reorder {
            eprintln!("warning: --generate-reorder is deprecated and ignored");
        }
    }
}

#[derive(Parser)]
pub struct Args {
    #[clap(flatten)]
    pub rocq_of_rust: RocqOfRustArgs,
    #[clap(last = true)]
    pub rust_flags: Vec<String>,
}

#[derive(Clone)]
pub struct Options {
    pub(crate) in_cargo: bool,
    pub(crate) axiomatize: bool,
    pub(crate) with_json: bool,
}

impl Options {
    pub fn from_args(rocq_of_rust: RocqOfRustArgs) -> Self {
        let cargo_rocq_of_rust = std::env::var("CARGO_ROCQ_OF_RUST").is_ok();

        Options {
            in_cargo: cargo_rocq_of_rust,
            axiomatize: rocq_of_rust.axiomatize,
            with_json: rocq_of_rust.with_json,
        }
    }
}
