# Contribute

Here we describe the architecture of the project to help contributions to the project.

## The `rocq-of-rust` command

The  `rocq-of-rust` command, called with `cargo rocq-of-rust`, is defined in the file [bin/cargo-rocq-of-rust.rs](../lib/src/bin/cargo-rocq-of-rust.rs). This file is a wrapper around the library [lib.rs](../lib/src/lib.rs) that defines the translation from Rust to Rocq.

We define all the translation from Rust to Rocq in Rust. This has following advantages:

- we can use the API of the Rust compiler to parse Rust code
- the resulting command is easy to integrate into an existing Rust project
- anyone who already knows Rust can contribute to the project
- this forces us to practice Rust on a daily basis

The translation is done in three steps:

1. translate the HIR representation of the Rust crate/file to our Rocq AST
2. apply a monadic translation to the Rocq AST
3. pretty-print the Rocq AST

### 1. From HIR to Rocq AST

### 2. Monadic translation

We apply a monadic translation to the whole code. The type of our monad is `M A`. We use the notation `let*` for the "bind" operator, and `Pure` for "return", to distinguish them from the Rust keywords `let` and `return`. We generate temporary variables named `α1`, `α2`, etc. for intermediate results that must go through a "bind".

### 3. Pretty-printing

We use the Rust library [pretty](https://github.com/Marwes/pretty.rs) to pretty-print our Rocq AST to a string with a maximum line width of 80 characters. The aim of the pretty-printing is to avoid having lines that are too long and unreadable. The whole goal is to know when to break lines and how to indent the code. We group the primitives we use from `pretty` in the [render.rs](../lib/src/render.rs) file. This helped to reduce and uniformize the size of the pretty-printing code.

## Rocq libraries

In order to compile the translated Rocq files, we need to define the standard library of Rust and a set of language primitives in Rocq. Indeed, these are dependencies for any code that we wish to translate.

This is done in the file [RocqOfRust.v](../RocqOfRust/RocqOfRust.v). This file depends on many other files as we wanted to split the definition of the Rust standard library in many files. This is to make it easier to navigate the code and to compile it.
