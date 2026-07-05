# Linking Generated Code

This document explains the linking step between generated Rocq-of-Rust code and
the typed simulation layer. To illustrate the process, we begin with a demo Rust
file, `add.rs`, which contains a simple increment function.

```rust
fn main() {
    print!("{}", add(10));
}

fn add(n: u32) -> u32 {
    return n + 1;
}
```

The mechanically generated Rocq-of-Rust file is usually unidiomatic, verbose, and hard to
reason about formally. Here our generated file contains the following translation of
`add`.

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

The goal is to connect the mechanically generated Rocq-of-Rust file above to a
more idiomatic functional specification.

In this case, the specification is:

```coq
Definition add_spec (n : u32) : u32 :=
  n +i 1.
```

Here `+i` is integer addition with the same wrapping behavior as Rust unsigned integer
arithmetic.

## Generated Translation

Running `rocq-of-rust` with `add.rs` as an input yields `add.v`. The generated `add`
definition has the following type signature:

```coq
Definition add (epsilon : list Value.t) (tau : list Ty.t) (alpha : list Value.t) : M := ...
```
Here we have:

- `epsilon`: constant generic arguments.
- `tau`: type generic arguments.
- `alpha`: runtime Rust arguments.
- `M`: the Rocq-of-Rust computation tree for the translated Rust code.

Inside the generated body, Rocq-of-Rust allocates the argument `n`, reads it,
calls the primitive wrapped addition operation with `1`, and returns the result.

## Link File

In this demo, `links/add.v` defines the following `Run.Trait` instance:

```coq
Instance run_add (n : u32) :
  Run.Trait Demo.add.add [] [] [φ n] u32.
```

`Run.Trait` is the typeclass used to link a generated Rocq-of-Rust function to
the typed computation exposed to the simulation layer. This instance says that
the untyped generated function `Demo.add.add`, when called with no generic
arguments and one runtime argument `φ n`, behaves as a typed computation
returning a `u32`.

In the translated program, runtime values are represented as `Value.t`, so `φ`
converts the typed Rocq value `n` into the untyped representation expected by
the generated translation.

The proof is:

```coq
Proof.
  constructor.
  run_symbolic.
Defined.
```

`constructor` starts the `Run.Trait` proof, and `run_symbolic` symbolically
executes the generated computation tree. For this straight-line function, the
tactic can discharge the proof automatically.

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

The proof is short because the link file has already shown that the generated
untyped function has a typed interpretation. The simulation proof only needs to
evaluate that linked interpretation.

`case n` exposes the integer payload inside the `u32` record. This lets the
argument `φ n` and the specification `n +i 1` reduce to concrete integer terms.

`eapply Run.Call` handles the call node produced by the linked body of `add`.
This call corresponds to the Rust expression `n + 1`, represented in the
generated file as a call to the wrapped-add primitive. The `Run.Call` constructor
splits the proof into two obligations:

- prove that the called computation evaluates to its intermediate result;
- prove that the continuation after the call evaluates to the final result.

The first `Run.Pure` closes the wrapped-add computation itself: after reduction,
the goal is the pure result `Output.Success (add_spec n)`. The second
`Run.Pure` closes the continuation, which simply returns that result. Since
there are no stack allocations left at this level, the final stack is still
`[]%stack`.

Thus we have seen how to start from a `.rs` file, generate a Rocq-of-Rust `.v`
file, link the generated function to a typed computation, and prove that it
evaluates to a small functional specification.
