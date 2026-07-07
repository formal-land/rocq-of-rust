# Linking a Mechanically Generated Rocq Program

This document explains the linking step between a mechanically generated Rocq program and
the typed simulation layer. We illustrate with a simple and concrete example.

## Prerequisites

The reader is expected to be comfortable with basic Rocq definitions, lemmas,
and proof scripts, as introduced in the [proof guide](./proof.md). The examples
also assume a working familiarity with the [`M`
computation tree](../../RocqOfRust/M.v#L485) of the mechanically generated Rocq
program, the untyped value representation
[`Value.t`](../../RocqOfRust/M.v#L232), and the embedding
[`φ`](../../RocqOfRust/links/M.v#L15) from typed Rocq values into generated
values.

No detailed knowledge of the linking internals is required. The point of the
example is to show how a mechanically generated Rocq program is packaged as a
typed computation with [`Run.Trait`](../../RocqOfRust/links/M.v#L1029), then
evaluated against a small functional specification with
[`SimulateM.eval_f`](../../RocqOfRust/simulate/M.v#L445).

## Introduction

We begin with the simple addition function below.

```rust
fn main() {
    print!("{}", add(10));
}

fn add(n: u32) -> u32 {
    return n + 1;
}
```

We want to be able to reason about this program formally. So we use Rocq-of-Rust to
obtain a mechanically generated Rocq program.

The mechanically generated Rocq program is usually unidiomatic, verbose, and hard to reason about formally.
This is what we have for the `add` function above.

```coq
Definition add (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [ n ] =>
    ltac:(M.monadic
      (let n := M.alloc (| Ty.path "u32", n |) in
      M.catch_return (Ty.path "u32") (|
        ltac:(M.monadic
          (M.never_to_any (|
            M.read (|
              M.return_ (|
                M.call_closure (|
                  Ty.path "u32",
                  BinOp.Wrap.add,
                  [ M.read (| n |); Value.Integer IntegerKind.U32 1 ]
                |)
              |)
            |)
          |)))
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.
```

The goal now is to relate the mechanically generated Rocq program above to a
more idiomatic functional specification. In this case, the specification is:

```coq
Definition add_spec (n : u32) : u32 :=
  n +i 1.
```

Here `+i` is integer addition with the same wrapping behavior as Rust unsigned integer
arithmetic.

## The Plan

The way we relate the mechanically generated Rocq program to the idiomatic specification
is by

1) Creating a link proving that the mechanically generated Rocq program behaves as
   a typed computation.

2) Showing that the linked computation evaluates to the idiomatic specification.

## On the mechanically generated Rocq program

In this demo, running `rocq-of-rust` with `add.rs` as an input yields
the mechanically generated Rocq program in `add.v`. The `add`
definition in that program has the following type signature:

```coq
Definition add (epsilon : list Value.t) (tau : list Ty.t) (alpha : list Value.t) : M := ...
```
Here we have:

- `epsilon`: constant generic arguments.
- `tau`: type generic arguments.
- `alpha`: runtime Rust arguments.
- `M`: the computation tree for the mechanically generated Rocq program.

Inside the mechanically generated Rocq program, Rocq-of-Rust allocates the
argument `n`, reads it, calls the primitive wrapped addition operation with `1`,
and returns the result.

## Generating the Link

In this demo, `links/add.v` defines the following `Run.Trait` instance:

```coq
Instance run_add (n : u32) :
  Run.Trait Demo.add.add [] [] [φ n] u32.
```

`Run.Trait` is the typeclass used to link a mechanically generated Rocq program to
the typed computation exposed to the simulation layer. This instance packages a proof
that the untyped entry point `Demo.add.add`, when called with no generic
arguments and one runtime argument `φ n`, behaves as a typed computation
returning a `u32`.

In the mechanically generated Rocq program, runtime values are represented as
`Value.t`, so `φ` converts the typed Rocq value `n` into the untyped
representation expected by the mechanically generated Rocq program.

The proof is:

```coq
Proof.
  constructor.
  run_symbolic.
Defined.
```

`constructor` starts the `Run.Trait` proof, and `run_symbolic` symbolically
executes the mechanically generated Rocq program. For this straight-line
function, the tactic can discharge the proof automatically.

## Simulation File

In this demo, `simulate/add.v` proves:

```coq
Lemma add_eq (n : u32) :
  {{
    SimulateM.eval_f (run_add n) []%stack 🌲
    (Output.Success (add_spec n), []%stack)
  }}.
```

The `🌲` notation is an evaluation judgment, not equality. It means that
evaluating the linked computation on the left produces the result on the right.
Here the lemma says that evaluating `run_add n` with an empty simulation stack
returns `Output.Success (add_spec n)` and leaves the stack empty.

The corresponding proof is:

```coq
Proof.
  case n.
  intros value.
  eapply Run.Call.
  ** apply Run.Pure.
  ** apply Run.Pure.
Qed.
```

The proof is short because the link file has already shown that the mechanically
generated Rocq program has a typed interpretation. The simulation proof only needs to
evaluate that linked interpretation.

`case n` exposes the integer payload inside the `u32` record. This lets the
argument `φ n` and the specification `n +i 1` reduce to concrete integer terms.

`eapply Run.Call` applies the [`Run.Call`](../../RocqOfRust/simulate/M.v#L484)
constructor to handle the call node produced by the linked body of `add`.
This call corresponds to the Rust expression `n + 1`, represented in the
mechanically generated Rocq program as a call to the wrapped-add primitive. The
`Run.Call` constructor splits the proof into two obligations:

- prove that the called computation evaluates to its intermediate result;
- prove that the continuation after the call evaluates to the final result.

The first [`Run.Pure`](../../RocqOfRust/simulate/M.v#L463) closes the wrapped-add
computation itself: after reduction, the goal is the pure result
`Output.Success (add_spec n)`. The second `Run.Pure` closes the continuation,
which simply returns that result. Since
there are no stack allocations left at this level, the final stack is still
`[]%stack`.

## Conclusion

So we have seen how to start from a `.rs` file, produce a `.v` file containing a
mechanically generated Rocq program, link that program to a typed computation,
and prove that it evaluates to a small functional specification.

The proofs for the link files and the simulation equivalence become more complex
as we translate more complex Rust programs. In subsequent files, we discuss proof
strategies for writing links and simulation equivalence proofs for Rust programs
that use more complex language constructs.

For repetitive record and enum link definitions, see the
[Rocq link plugin](./link-plugin.md).
