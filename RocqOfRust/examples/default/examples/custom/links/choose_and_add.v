Require Import links.RocqOfRust.
Require Import examples.default.examples.custom.choose_and_add.

Instance run_choose_u32 (take_left : bool) (left right : u32) :
  Run.Trait choose_u32 [] [] [φ take_left; φ left; φ right] u32.
Proof.
 constructor.
 run_symbolic.
Defined.
Global Opaque run_choose_u32.

Instance run_add_pair (pair : u32 * u32) :
  Run.Trait add_pair [] [] [φ pair] u32.
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_add_pair.

Instance run_choose_and_add
    (take_left : bool)
    (pair : u32 * u32)
    (offset : u32) :
  Run.Trait choose_and_add [] [] [φ take_left; φ pair; φ offset] u32.
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_choose_and_add.    






