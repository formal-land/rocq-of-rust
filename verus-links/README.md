# Checking Verus assertions against Rust execution in Rocq

`rocq-of-rust verus` reads a typed Verus assertion, generates its Rocq meaning, translates the Rust function body, and replays a handwritten proof that connects them. The indexed loop gives a case in which Verus reports an open obligation and Rocq proves the same source postcondition over the translated execution. [Checked results and assumptions](RESULTS.md)

## Try the fallback

Run these commands from the repository root with the built CLI, Verus and Rocq on the path. The first command removes the loop invariant that tells Verus what happens to the suffix. The executable Rust and all three postconditions stay the same.

```bash
work=$(mktemp -d)
sed '/forall|j: int| i <= j < old(xs)/d' verus-links/fill.rs > "$work/fill.rs"
rocq-of-rust verus --path "$work/fill.rs" --function fill_prefix \
  --at 11:9 --proof verus-links/FillSuffixProof.v --output-path "$work/results"
```

Verus points to `final(xs)@[j] == old(xs)@[j]` for `n <= j < old(xs)@.len()`. The Rocq proof characterizes the entire slice after iteration `i` as `repeat value i ++ skipn i initial`. Each iteration writes one in-bounds element. At `i = n`, looking up any index in the suffix gives the same result as looking it up in the initial slice. The execution theorem also restores the caller’s entire stack frame. [Rust source](fill.rs) · [Execution statement](FillLink.v) · [Proof by induction](FillProof.v)

| CLI exit | Meaning |
|---|---|
| 0 | Verus verified the crate. Export succeeded, and any requested proof checked. |
| 1 | Input, translation, or proof replay failed. The report identifies the failing stage. |
| 2 | Rocq checked the selected execution property. Verus still reports an open or inconclusive obligation in the crate. |
| 3 | Export succeeded with an open or inconclusive Verus result. The run requested export only. |

Each invocation creates a fresh directory and prints its path. It contains `result.json`, the Rust snapshot and SHA-256, the typed VIR, Verus diagnostics, the translated Rust body, and `BridgeContract.v` with source ranges in the JSON report. When a proof checks, `Replay.log` records its Rocq assumptions. Drop `--at` to select the complete postcondition or omit `--proof` to export. A successful Rocq result is scoped to the named theorem. Verus continues to report its own whole-crate result.

## Memory examples

| Function | Executable property |
|---|---|
| `nested::swap` | Two disjoint mutable borrows into a nested record exchange their fields. The outer sentinel keeps its initial value. [Rust](nested.rs) · [Proof](SwapProof.v) |
| `nested::left_mut` | The result is the pointer to the nested left field. Its initial target equals the entry field. For every later write through this pointer, the parent at borrow expiry contains the written value and preserves its other fields. [Execution statement](BorrowLink.v) · [Proof](BorrowProof.v) |
| `nested::write_twice` | A real caller invokes the accessor and writes twice. The second write determines the final field. The sibling and sentinel survive. [Proof](TwiceProof.v) |
| `fill::fill_prefix` | For every valid 64-bit `usize` bound up to the slice length, the loop terminates and fills exactly the prefix, including the empty and full cases. Both ordinary and compound counter assignment replay. [Proof](FillProof.v) |
| `checkpoint::set_word` | An erased inline assertion after a write reads the value at that program point. Moving it before the write invalidates the source anchor. [Rust](checkpoint.rs) · [Execution statement](CheckpointLink.v) |

## Writing an execution link

The supported input is a standalone Rust file using `#[cfg_attr(verus_only, verus_spec(...))]` contracts. Both tools read the same staged file. The shared-body check admits gated Verus imports and proof blocks and rejects conditional executable statements and executable macro expansion. The examples exercise safe, exclusive references to records and mutable slices of `u32` on x86-64 Linux.

The exporter checks typed single-variant record projections and resolved slice-view operations. It emits syntax for scalar observations, sequence length and lookup, integer comparisons, mathematical addition and subtraction, conjunction, implication, and universal quantification over integers. The interpreter distinguishes entry, current and borrow-expiry observations. A bounded quantified lookup requires an actual element. Index expressions in premises need additional definedness machinery and currently produce a diagnostic. Machine-word and stack validity are obligations of the execution link. [VIR adapter](vir_contract.py) · [Assertion language and interpretation](Assertion.v)

A proof named `FooProof.v` has a sibling `FooLink.v`. The link defines `linked_function`, `linked_site`, the supported `observed_paths`, and `execution_claim`, parameterized by the interpreted precondition and selected assertion. Its author identifies the translated function, relates observations to real stack slots or pointer operations, and states what successful execution establishes. For an inline assertion or loop invariant the link also records `linked_source_sha256` to anchor the reviewed program point. The proof exports `checked_execution`. Replay checks its type against the regenerated claim, checks that the link covers each observation, and compares the theorem’s assumptions with those of the reviewed statement. Local proof dependencies use ordinary unqualified `Require Import` or `Require Export` from sibling source files. [Small worked link](SwapLink.v) · [Source-anchored link](CheckpointLink.v)

The hand-authored link is part of the specification a reviewer must read. Rocq checks the proof about rocq-of-rust's model. Trust also includes the pinned VIR adapter, Rust translation, the model’s existing declarations, and the interpretation of the supported Verus operations. Importing a proof into Verus would additionally require a checked connection to its verification condition.

## Build and replay

The checked configuration uses Verus `0.2026.11.02.8bf68ee` with Rust 1.99.1, rocq-of-rust's `nightly-2025-12-07`, and Rocq 9.0.1 with impredicative Set. The library and plugin must match the Rocq compiler. Python 3.10 or later runs the adapter.

```bash
cargo build --locked --bin rocq-of-rust
make -C RocqOfRust simulate/RocqOfRust.vo
export PATH="$PWD/target/debug:$PATH"
export ROCQ_OF_RUST_LIB="$PWD/RocqOfRust"
export RUSTUP_TOOLCHAIN=nightly-2025-12-07
export LD_LIBRARY_PATH="$(rustc --print sysroot)/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
python3 verus-links/replay_examples.py --output-path /tmp/verus-bridge-replay
```

Set `VERUS` or `COQC` to select tool executables. `ROCQ_OF_RUST_BRIDGE` locates the bridge directory if the executable is moved away from its build checkout. The suite regenerates every body and contract, creates the weakened invariant and mutation controls in scratch space, and replays the original pair experiment. [Test cases](replay_examples.py) · [Original pair experiment](PAIR.md)
