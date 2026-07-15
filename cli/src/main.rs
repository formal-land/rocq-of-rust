#![feature(rustc_private)]

extern crate rocq_of_rust_lib;

use std::path::{Path, PathBuf};

use clap::Args;
use clap::{Parser, Subcommand};

#[derive(Args)]
struct Translate {
    /// Sets a path to rust file
    #[arg(short, long, value_name = "PATH", value_parser = is_valid_path)]
    path: PathBuf,
    /// Axiomatize the definitions
    #[arg(long, value_name = "axiomatize", default_value_t = false)]
    axiomatize: bool,
    /// Output path where to place the translation
    #[arg(long, value_name = "output_path", value_parser = is_valid_path, default_value = "rocq_translation")]
    output_path: PathBuf,
    /// Generate a table mapping Rust function paths to their Rocq definitions
    #[arg(long, default_value_t = false)]
    with_function_table: bool,
}

fn is_valid_path(path: &str) -> Result<PathBuf, String> {
    let target_path = Path::new(path);
    if target_path.exists() {
        Ok(target_path.to_path_buf())
    } else {
        Err(format!("Path does not exist: {path}"))
    }
}

#[derive(Subcommand)]
enum Commands {
    /// Translate rust files to Rocq files
    Translate(Translate),
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
        Commands::Translate(t) => {
            println!("Translating: {}", &t.path.display());
            core::run(core::CliOptions {
                path: t.path,
                output: t.output_path,
                axiomatize: t.axiomatize,
                with_function_table: t.with_function_table,
            });
            println!("Finished.");
        }
    }
}
