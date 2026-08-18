Require Import links.RocqOfRust.
Require Import examples.default.examples.custom.pattern_matching_references.

Instance run_match_value (value : u32) :
  Run.Trait match_value [] [] [φ value] u32.
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_match_value.

Instance run_match_ref (value : u32) :
  Run.Trait match_ref [] [] [φ value] u32.
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_match_ref.

Instance run_match_ref_mut (value : '&mut u32) :
  Run.Trait match_ref_mut [] [] [φ value] u32.
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_match_ref_mut.

Instance run_match_reference (value : '& u32) :
  Run.Trait match_reference [] [] [φ value] u32.
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_match_reference.

Instance run_match_mutable_reference (value : '&mut u32) :
  Run.Trait match_mutable_reference [] [] [φ value] u32.
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_match_mutable_reference.
