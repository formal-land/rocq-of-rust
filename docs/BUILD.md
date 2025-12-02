# Installation and Build Tutorial

This tutorial provides an introduction to how to build `rocq-of-rust`.
The first part of the tutorial describes two possible ways to build
the Rust to Rocq translator (implemented in Rust): as a cargo plugin or
as a standalone executable. The second part of the tutorial describes
how to install dependencies and build the Rocq implementation of Rust
shallow embedding and facilities to verify Rust programs. After you
successfully built `rocq-of-rust` you can take a look at our [user
guide](./GUIDE.md)

## Table of Contents

- [Rust](#rust)
  - [Cargo plugin](#cargo-plugin)
  - [Standalone executable](#standalone-executable)
  - [Tests](#tests)
- [Rocq](#rocq)
- [For Windows](#for-windows)

## Rust

### Cargo plugin

In order to install `rocq-of-rust` run the following command from the
root of this repository:
```sh
cargo install --path lib/
```

This command would build and install the `rocq-of-rust` library and
the cargo plugin.

Then, in any Rust project, generate a `Crate.v` file with the Rocq
translation of the crate using this command:
```sh
cargo rocq-of-rust
```

See the `rocq-of-rust` [user guide](./GUIDE.md) for more details about
using `rocq-of-rust`.

### Standalone executable

Additionally, it is also possible to build `rocq-of-rust` as a
standalone executable. This method has an advantage of supporting the
translation of individual files, while the cargo plugin only supports
the translation of the whole crates.

The following command would build `rocq-of-rust` as a standalone
executable (in release mode):
```sh
cargo build --bin rocq-of-rust --release
```

Using `rocq-of-rust` as a standalone executable is intended for testing
purposes. We generally recommend to use the cargo plugin instead.

### Tests

The following command allows to regenerate the snapshots of the
translations of the test files:
```sh
python run_tests.py
```

If `rocq-of-rust` would fail to translate some of the test files, it
would produce a file with an error instead.

Check if some freshly generated translation results differ to those
included in the repository:
```sh
git diff
```

## Rocq

In order to install dependencies and build the Rocq part of the project
run the following commands.

Create a new opam switch:
```sh
opam switch create rocq-of-rust ocaml.5.1.0
```

Update shell environment to use the new switch:
```sh
eval $(opam env --switch=rocq-of-rust)
```

Add the repository with Rocq packages:
```sh
opam repo add rocq-released https://rocq.inria.fr/opam/released
```

Go to the directory with Rocq files:
```sh
cd RocqOfRust
```

Install the required dependencies:
```sh
opam install --deps-only .
```

Compile the Rocq files:
```sh
make
```


## For Windows

On Windows, to set up the environment for translating your Rust project, 
follow the belows:

1. Install WSL 2 by [the official tutorial](https://learn.microsoft.com/en-us/windows/wsl/install) with a proper Linux distribution
2. Install [Rocq](https://rocq.inria.fr/download) in WSL 2
3. Install [VSCode](https://code.visualstudio.com/), its [WSL](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-wsl) 
extension and its [Rocq](https://marketplace.visualstudio.com/items?itemName=ruoz.rocq) 
extension
4. Follow the [official guide](https://code.visualstudio.com/docs/remote/wsl) 
to run the Rocq project in WSL environment. Specifically:
   1. With an WSL terminal, enter `code .` at the project root that 
   you want to run `RocqOfRust`
   2. With `Ctrl+,` for VSCode's settings, checkout the environment 
   settings for `Remote: [WSL ...]`. Modify the `Rocq: Rocq Project Root` 
   to `.` , in particular, your preference folder with `_RocqProject` 
   inside
   3. Now you can `make` your project in WSL(not Windows) or customize 
   your experience with other features of `RocqOfRust`

### Known Issues

[WSL has a different file format from Windows](https://blog.jyotiprakash.org/the-windows-file-system-and-the-wsl-file-systems-are-different)
(Also [here](https://learn.microsoft.com/en-us/windows/wsl/filesystems)). 
Since we run Rocq on WSL only, the files being generated should be in 
WSL's file format. We usually put the project on Windows, `make` it 
in WSL, to generate Rocq files of WSL's file format. The format differences 
here usually lead to significantly longer `make` time for WSL than other 
systems. 

As an alternative, you might copy the project under WSL's `/home` and
observe the performance boost under WSL's `make`, with a tradeoff of
extra time on copying the project from Windows to WSL.