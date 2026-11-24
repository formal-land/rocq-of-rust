#![feature(rustc_private)]

use clap::*;
use rocq_of_rust_lib::{callbacks::CARGO_SELECTION, options::Args};
use std::{
    env,
    hash::{DefaultHasher, Hash, Hasher},
    process::{exit, Command},
};

fn main() {
    let args = Args::parse_from(std::env::args().skip(1));

    args.rocq_of_rust.warn_deprecated();

    let rocq_of_rust_rustc_path = std::env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("rocq-of-rust-rustc");

    let cargo_path = env::var("CARGO_PATH").unwrap_or_else(|_| "cargo".to_string());
    let cargo_cmd = if std::env::var_os("ROCQ_OF_RUST_CONTINUE").is_some() {
        "build"
    } else {
        "check"
    };
    let mut cmd = Command::new(cargo_path);
    // Cargo can reuse a workspace member's dependency check when it later
    // becomes a primary package. Make that change visible in rustc dep-info.
    let directory = env::current_dir().expect("current working directory");
    let mut selection = DefaultHasher::new();
    (directory, &args.rust_flags).hash(&mut selection);
    cmd.env(CARGO_SELECTION, selection.finish().to_string());
    cmd.arg(cargo_cmd)
        .args(args.rust_flags)
        .env("RUSTC_WORKSPACE_WRAPPER", rocq_of_rust_rustc_path)
        .env("CARGO_ROCQ_OF_RUST", "1");

    cmd.env(
        "ROCQ_OF_RUST_ARGS",
        serde_json::to_string(&args.rocq_of_rust).unwrap(),
    );

    let exit_status = cmd.status().expect("could not run cargo");
    if !exit_status.success() {
        exit(exit_status.code().unwrap_or(-1));
    }
}
