# Interpreting Verus assertions over rocq-of-rust executions

This experiment connects an actual Verus postcondition to the execution of an actual translated Rust function. The assertion language lives in a Rocq library above the execution model. The proposed division of responsibility is that Verus supplies the typed formula and rocq-of-rust supplies witnesses for the program values, heap observations and lifetimes appearing in that formula.

## Evidence

The single Rust source uses `cfg_attr` to enable Verus contracts. Both compilers see one copy of each function body. Verus verified all three functions with `--no-cheating`. The Python exporter reads the three typed VIR postconditions and generates shallow Gallina predicates. Rocq-of-rust separately translates the bodies. Rocq 9.0.1 checked proofs of all three exported contracts about these bodies. The prototype pins the function signatures and accepts a small grammar of `u32` observations, specification equality and conjunction. It reads a version-specific debug dump. A production implementation should consume typed VIR directly. [Rust](pair.rs) · [Exporter](export_contracts.py) · [Generated predicates](Contracts.v) · [Generated execution model](pair.v)

| Function | What the Rocq proof connects |
|---|---|
| `copy_right(p)` | The entry stack contains the original record. The successful return stack contains a record whose two fields equal the original right field. |
| `left_mut(p)` | The returned pointer is the subpointer to the left field. The return stack still contains the original record. For every later value written through this field pointer, its update operation makes the left field equal to that value and preserves the original right field. |
| `write_through(p, v)` | A caller invokes the translated accessor, writes through the returned pointer, and returns with the updated record. This checks composition for an actual client, for arbitrary input and written value. |

For `left_mut`, the contract observes the returned reference twice. Dereferencing it at return gives the initial left field. Dereferencing it at borrow expiry gives the later value. Taking the parent record at function return for both observations makes the translated claim false. Rocq checks that counterexample with initial fields 10 and 20 and a later write of 100. A separate negative control changed `copy_right`'s first postcondition to say that the left field kept its original value. Verus rejected it, the exporter changed the corresponding equality, and Rocq rejected the execution proof. [Execution proofs and counterexample](PairProof.v) · [Verus semantics of mutable references](https://github.com/verus-lang/verus/blob/439c01c78eb6e6f0a85b43d43fdcd29d2af49f47/source/docs/guide/src/mutable-references.md)

## How much semantics has to agree?

A common interpretation can permit multiple representations. For this fragment, choosing a word representation that preserves and reflects equality gives equivalent meanings for the whole borrow postcondition. Rocq checked that theorem as well as a counterexample where collapsing every word to one value makes a false contract provable. The theorem is closed under the global context. Equality is sufficient here. A larger fragment needs correspondence for every operation it adds, including bounds, casts, overflow and equality of sequences. For quantifiers it also needs a precise domain of represented values. For example, an encoding of `u32` into integers restricts a universal quantifier to integers between zero and 2³²−1. [Representation theorem](View.v)

The observation called `final` has one intended meaning tied to the end of a borrow. Its implementation in Rocq depends on the borrow. For a nonescaping input, an output stack at return can supply it. For a returned field borrow, the update function of a typed field subpointer relates the parent's eventual value to the child's. This experiment uses the second rule for one exclusive reference to a fixed record on a singleton stack. The universal quantification ranges over future field values. A semantics for general client executions would also have to show how every permitted sequence of reborrows, writes and loan expiries satisfies that relation, with a frame for unrelated memory. [Subpointer read/write laws](../RocqOfRust/links/M.v)

I would give each supported Verus construct a compositional interpretation in Rocq, and each executable use a separate correspondence lemma with the Rust state. Pure ghost values can live entirely in the assertion library. For example a sequence view of a vector would require lemmas connecting length, lookup and mutation to the concrete vector model, including the specification's behavior outside its recommended index range. Tracked tokens and atomic invariants need additional ownership or protocol semantics. They cannot be recovered from a pair of heaps alone. VerusBelt offers a Rocq/Iris account of several such constructs. [Verus sequence interface](https://github.com/verus-lang/verus/blob/439c01c78eb6e6f0a85b43d43fdcd29d2af49f47/source/vstd/seq.rs) · [VerusBelt](https://github.com/verus-lang/verus-belt)

## What a proof can discharge

The semantics-level theorem for a function combines its translated body, its preconditions, and the interpreted postcondition. A Verus diagnostic for an intermediate assertion additionally needs proof of the context at that program point, including path assumptions, call contracts, ghost state and the current borrow state. An erased assertion may have no corresponding executable instruction. Name the point on the Verus side and relate it to the Rocq execution if needed.

To credit a Rocq proof in Verus, either check an implication to the actual Verus VC in its scoped theory, or implement a rule that admits a source-level lemma once its semantic interpretation and all required model-correspondence obligations are checked. Proving a formula in one selected heap or ghost model is insufficient if Verus allows other observations that violate it. The working example targets the source-level route. Export of the supported postconditions is automatic. The witness and execution proofs are handwritten. Upstream Verus does not consume the resulting proof.

The execution theorems depend on rocq-of-rust's model declarations and impredicative Set. The caller theorem additionally uses the translator's admitted function-lookup registration for `pair::left_mut`. The other two execution theorems refer directly to their translated functions. The extractor is experimental trusted code, with no mechanized proof of VIR translation correctness.

## Reproduce

The base is rocq-of-rust `ca1374ae2`, the translator's pinned nightly is `nightly-2025-12-07`, and the Verus release is `0.2026.11.02.8bf68ee` on Rust 1.99.1. Run in a scratch copy of this directory with the matching tools. Set `ROCQ_OF_RUST_LIB` to a compiled RocqOfRust directory from the base revision.

```bash
verus --crate-type lib --no-cheating --log vir pair.rs
python3 export_contracts.py .verus-log/crate.vir Contracts.v
rocq-of-rust translate --path pair.rs --output-path .
for f in Contracts pair View PairProof; do
  coqc -Q . "" -R "$ROCQ_OF_RUST_LIB" RocqOfRust -I "$ROCQ_OF_RUST_LIB/plugin" \
    -impredicative-set "$f.v" || exit 1
done
```
