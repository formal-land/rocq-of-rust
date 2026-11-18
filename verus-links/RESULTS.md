# Verification results

The suite rebuilt the Rust translations, regenerated the assertions from Verus VIR, and compiled the proof sources with Rocq. The missing-invariant case produced **one open Verus postcondition and a checked Rocq execution theorem for that same source clause**. The verifier identified the suffix at `fill.rs:11:9`. Removing the invariant left the generated `fill_prefix` definition byte-identical. [Verus diagnostic](evidence/fill-suffix-verus.txt) · [Generated Rocq assertion](evidence/FillSuffixContract.v) · [Kernel assumptions report](evidence/fill-suffix-assumptions.txt)

| Input and property | Verus checks verified / errors for the crate | Rocq outcome |
|---|---|---|
| Nested field swap | 3 / 0 | Checked swap and sentinel preservation |
| Nested field accessor | 3 / 0 | Checked returned field pointer and both borrow observations |
| Caller writing through accessor twice | 3 / 0 | Checked second write and frame |
| Source-selected inline assertion | 1 / 0 | Checked the observation after the assignment |
| Full prefix loop contract | 2 / 0 | Checked all inputs satisfying the bound and all caller frames |
| Loop-head suffix invariant selected by source position | 2 / 0 | Exported the selected invariant |
| Omit suffix invariant, select complete contract | 1 / 1 | Checked the complete contract |
| Omit suffix invariant, select the reported clause | 1 / 1 | Checked `ensures_2` |
| Spell the increment `i += 1` | 2 / 0 | Same proof checked against a separate translation |

Verus numbers refer to the entire crate for each invocation. The nested rows share one Rust file. The three original pair execution theorems and the observation representation checks also replayed, with Verus reporting 3 verified and 0 errors for that crate. [Original experiment](PAIR.md)

## Negative controls

- Changing the caller’s postcondition to require its first argument as the final field value makes both tools reject the claim. Changing only the executable second write also breaks the previous proof.
- Moving the inline assertion before its write changes the reviewed program point. Verus reports the assertion and the Rocq replay rejects the stale source anchor, even though erasure produces the same executable code.
- Replacing the expected theorem with a proof of `True` fails the type check. Declaring the expected theorem as an axiom fails the assumptions comparison.
- An unsupported inequality form produces a source-located adapter error. Using conditional compilation on the second executable write fails the shared-body check. Renaming an ordinary Rust function still produces an export.

## Proof assumptions

For the swap, accessor, checkpoint and slice theorems, including both fallback runs, `Print Assumptions` lists ten existing model or primitive-string declarations plus impredicative Set. All eight positive proof replays had the same set of assumptions as their respective execution statements. The caller also uses the admitted function-lookup registration `nested.Instance_IsFunction_left_mut` emitted by rocq-of-rust. The proofs of slice updates, bounds and loop termination introduce no new axioms. [Slice theorem audit](evidence/fill-suffix-assumptions.txt) · [Caller theorem audit](evidence/caller-assumptions.txt)

The input loop uncovered two issues in rocq-of-rust. The simulator previously returned a placeholder for every loop. Its finite execution rules now thread the stack through each iteration. A second issue arose when a temporary in a built-in compound assignment could run before a preceding slice write. The Rocq notation now elaborates the existing let-bound read and write using the right-hand side before the destination, and the suite replays both counter spellings. [Loop rules](../RocqOfRust/simulate/M.v) · [Compound assignment](../RocqOfRust/M.v)

## Reproduction

Tested on x86-64 Linux with Verus commit `8bf68ee741df833ea5d0fe6a2255126fdea87e47` and its Rust 1.99.1 toolchain. The Rust translator used `rustc 1.94.0-nightly (ba86c0460 2025-12-06)`. The offline checker used Rocq 9.0.1 and its matching plugin. The suite records fresh source hashes, scopes, outcomes, and per-module logs in its output directory. [Build and replay commands](README.md#build-and-replay) · [Full test driver](replay_examples.py)

On the original machine, the toolchain cache and offline container can also replay the suite. The following commands use the existing local build while its scratch directory is available.

```bash
source /tmp/bridge-dev/env
podman --root /tmp/verus-rocq-tools.F0kJ42/podman-root \
  --runroot /tmp/verus-rocq-tools.F0kJ42/podman-run --storage-driver vfs \
  start rocq-verus-fill-check
python3 verus-links/replay_examples.py --output-path /tmp/bridge-dev/replay
```
