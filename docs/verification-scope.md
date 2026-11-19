# Verification scope

The semantic checks run a Rust executable and compile Rocq witnesses for its translated operations with the pinned toolchain. The native arithmetic fixture uses disabled overflow checks. The integer model uses 64-bit pointer-sized integers. The evaluator reports `Execution.Unsupported` for an unsupported operation and for a panic.

| Public simulation | Hypotheses on the input or callback | Compiler or representation assumptions |
|---|---|---|
| `Option::map` | The callback takes a one-element tuple. Its simulation supplies a successful return with an unchanged stack. In the `None` case the unused callback must have trivial drop glue. | The external premise `callback_has_trivial_drop` applies to the particular callback value and type. Its truth depends on the Rust captures. |
| Slice `len` and `is_empty` | A readable reference to a slice represented by a list. | `SliceMetadata.metadata_type` gives the slice metadata type. `SliceMetadata.body` specifies the compiler intrinsic on a pointer to that slice. The length is the element count, including zero-sized elements. |
| `Vec::len` and `Vec::is_empty` | A readable reference and `Vec.valid_length`. | The layout parameter `Vec.size_of` supplies the element size. `Vec.max_slice_len_value` connects the associated constant to that layout. The upper bound is `usize::MAX` for size zero and `isize::MAX / size` for positive sizes. The buffer representation uses `RawVec.to_value`. |

The witnesses use the project's abstract Rust type representation, generated function and method lookup instances, primitive strings, and impredicative Set. The shared simulation interpreter also depends on `SimulateM.TodoLoop`. Running `tests/semantics/check.sh target/debug/rocq-of-rust` prints the kernel's assumption reports for all five public theorems and compares their dependency names with `tests/semantics/assumptions.expected`. A changed dependency list requires review. The full report also prints the types of the assumptions.

## Unsupported source constructs

| Warning | Meaning |
|---|---|
| `ROR001` | A value-carrying break or const-continue. |
| `ROR002` | An explicitly labeled break or continue. |
| `ROR003` | A floating-point literal. |

These checks stop the affected expression. Implicit Rust destruction remains a release blocker (T12). The release translator omits implicit drops. An execution proof for translated code can therefore miss Rust side effects on a scope exit or when a callback goes unused. In particular, byte-for-byte preservation of the Revm success proofs does not establish equivalence for an owned account that needs drop glue.

The companion branch `experimental/implicit-drop-guard` emits `ROR004` and guards potential normal-path drops using rustc's MIR after drop elaboration. It handles selected Boolean and enum branches, but can reject a Revm early return before any account has been acquired.
