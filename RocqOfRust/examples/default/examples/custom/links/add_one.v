Require Import links.RocqOfRust.
Require Import examples.default.examples.custom.add_one.

Instance run_add_one (x : u32) : Run.Trait add_one [] [] [φ x] u32.
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_add_one.
