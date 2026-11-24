#![feature(rustc_private)]

extern crate rocq_of_rust_lib;

mod verus_input;

use std::path::{Path, PathBuf};

use clap::Args;
use clap::{Parser, Subcommand};

#[derive(Args)]
struct Translate {
    /// Sets a path to rust file
    #[arg(short, long, value_name = "PATH", value_parser = is_valid_path)]
    path: PathBuf,
    #[arg(long, hide = true)]
    check_verus_input: bool,
    /// Axiomatize the definitions
    #[arg(long, value_name = "axiomatize", default_value_t = false)]
    axiomatize: bool,
    /// Output path where to place the translation
    #[arg(long, value_name = "output_path", value_parser = is_valid_path, default_value = "rocq_translation")]
    output_path: PathBuf,
}

fn is_valid_path(path: &str) -> Result<PathBuf, String> {
    let target_path = Path::new(path);
    if target_path.exists() {
        Ok(target_path.to_path_buf())
    } else {
        Err(format!("Path does not exist: {path}"))
    }
}

#[derive(Args)]
struct Verus {
    /// Standalone Rust file containing cfg_attr Verus specifications
    #[arg(long)]
    path: PathBuf,
    /// Rust function name, optionally qualified by its crate
    #[arg(long)]
    function: String,
    /// Directory for fresh, isolated verification runs
    #[arg(long)]
    output_path: PathBuf,
    /// Select an assertion at LINE:COLUMN
    #[arg(long)]
    at: Option<String>,
    /// Handwritten Rocq execution proof
    #[arg(long)]
    proof: Option<PathBuf>,
}

#[derive(Subcommand)]
enum Commands {
    /// Translate rust files to Rocq files
    Translate(Translate),
    /// Export a typed Verus assertion and optionally replay its Rocq proof
    Verus(Verus),
}

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,

    /// Turn debugging information on
    #[arg(short, long, action = clap::ArgAction::Count)]
    debug: u8,
}

fn main() {
    use rocq_of_rust_lib::core;
    let cli = Cli::parse();

    match cli.command {
        Commands::Verus(v) => {
            let directory = std::env::var_os("ROCQ_OF_RUST_BRIDGE")
                .map(PathBuf::from)
                .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("../verus-links"));
            let mut command = std::process::Command::new("python3");
            command
                .arg(directory.join("check_bridge.py"))
                .arg("--translator")
                .arg(std::env::current_exe().expect("current executable"))
                .arg("--path")
                .arg(v.path)
                .arg("--function")
                .arg(v.function)
                .arg("--output-path")
                .arg(v.output_path);
            if let Some(at) = v.at {
                command.arg("--at").arg(at);
            }
            if let Some(proof) = v.proof {
                command.arg("--proof").arg(proof);
            }
            match command.status() {
                Ok(status) => std::process::exit(status.code().unwrap_or(1)),
                Err(error) => {
                    eprintln!("could not launch Verus bridge: {error}");
                    std::process::exit(1);
                }
            }
        }
        Commands::Translate(t) => {
            if t.check_verus_input {
                if let Err(error) = verus_input::check(&t.path) {
                    eprintln!("unsupported dual-mode input: {error}");
                    std::process::exit(1);
                }
            }
            println!("Translating: {}", &t.path.display());
            core::run(core::CliOptions {
                path: t.path,
                output: t.output_path,
                axiomatize: t.axiomatize,
            });
            println!("Finished.");
        }
    }
}
