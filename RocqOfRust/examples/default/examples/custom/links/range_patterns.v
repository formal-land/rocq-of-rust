Require Import links.RocqOfRust.
Require Import examples.default.examples.custom.range_patterns.

Instance run_classify (x : u8) :
  Run.Trait classify [] [] [φ x] u8.
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_classify.
