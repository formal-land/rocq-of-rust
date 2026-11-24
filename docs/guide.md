# User Tutorial

This tutorial provides some examples and tips for using `rocq-of-rust`
as well as a list of supported command line options and their
description. The first part of the tutorial describes the cargo plugin
version of `rocq-of-rust`, while the second part describes the
standalone executable version. Note that these two versions of
`rocq-of-rust` support different sets of command line options. See our
[build tutorial](./builds.md) for instructions on how to build either
of those versions of `rocq-of-rust`.

## Table of Contents

- [Cargo plugin](#cargo-plugin)
  - [Example](#example-0)
  - [Tips](#tips-0)
  - [Interface](#interface-0)
- [Standalone executable](#standalone-executable)
  - [Example](#example-1)
  - [Tips](#tips-1)
  - [Interface](#interface-1)

## Cargo plugin

### Example

From a Cargo crate, generate one Rocq module per source file and a crate export index with this command.
```sh
cargo rocq-of-rust
```

### Tips

Sometimes the execution of the above command might result with an
error related to Rust library versions mismatch. In that case, copy
the `rust-toolchain` config file (which can be found in the root of
this repository) to the root of the Rust project you want to generate
the translation of.

### Interface

Usage: `cargo rocq-of-rust [OPTIONS] [-- <RUST_FLAGS>...]`

Arguments:
  `[RUST_FLAGS]...`

Options:
- `--axiomatize`
  Axiomatize the definitions
- `-h`, `--help`
  Print help

- `--with-json` also writes the translation as JSON.
- `--configuration-file` and `--generate-reorder` are deprecated and ignored.
  Supplying either option prints a warning.

## Standalone executable

### Example

The following command can be used to translate one of the
`rocq-of-rust` test examples:
```sh
./rocq-of-rust translate --path examples/rust_book/hello_world/hello_world.rs
```

### Tips

Using `rocq-of-rust` as a standalone executable is intended for testing
purposes. We generally recommend to use the cargo plugin instead.

### Interface

Usage: `rocq-of-rust [OPTIONS] <COMMAND>`

Commands:
- `translate` Translate rust files to rocq files
- `help`      Print this message or the help of the given subcommand(s)

Options:
- `-d`, `--debug...` Turn debugging information on
- `-h`, `--help`     Print help
- `-V`, `--version`  Print version

#### Translate subcommand

Usage: `rocq-of-rust translate [OPTIONS] --path <PATH>`

Options:
- `-p`, `--path <PATH>`           Rust source file or directory with one conventional crate root
- `--axiomatize`                  Axiomatize the definitions
- `--output-path <output_path>`   Output path where to place the translation `[default: rocq_translation]`
- `-h`, `--help`                  Print help


A directory input must contain exactly one of `src/lib.rs`, `src/main.rs`, `lib.rs`,
and `main.rs`. When a package has both a library and a binary, pass the desired
source file explicitly. The translator creates the output directory and writes
each source module to its corresponding relative path.
