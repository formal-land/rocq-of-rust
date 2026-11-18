Require Import core.links.result.
Require Import revm.revm_precompile.simulate.bls12_381.utils.
Require Import revm.revm_precompile.simulate.bls12_381_const.
Require Import revm.revm_precompile.simulate.interface.
Require Import simulate.RocqOfRust.
From Stdlib Require Import List ZArith.

Import ListNotations.
Open Scope Z_scope.

Module bls12_381_utils.
  (** Release-mode u64 wrapping is explicit at both Rust multiplications.
      The discount table is nonempty, as in both callers. *)
  Definition msm_required_gas (k : usize) (discount_table : list u16)
      (multiplication_cost : u64) : u64 :=
    if Z.eqb k.(Integer.value) 0 then {| Integer.value := 0 |} else
    let index := Z.min (k.(Integer.value) - 1)
      (Z.of_nat (List.length discount_table) - 1) in
    let discount := List.nth (Z.to_nat index) discount_table {| Integer.value := 0 |} in
    let product := (k.(Integer.value) mod 2 ^ 64 * discount.(Integer.value)) mod 2 ^ 64 in
    {| Integer.value := ((product * multiplication_cost.(Integer.value)) mod 2 ^ 64) / bls12_381_const.MSM_MULTIPLIER.(Integer.value) |}.
End bls12_381_utils.
