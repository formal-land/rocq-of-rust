From Stdlib Require Import Bool List ZArith.

Require Import revm.revm_precompile.simulate.bn254.
Require Import revm.revm_precompile.simulate.bn254_final_exp.
Require Import revm.revm_precompile.simulate.bn254_miller.
Require Import revm.revm_precompile.simulate.bn254_pairing.
Require Import revm.revm_precompile.simulate.bn254_tower.

Import ListNotations.
Open Scope Z_scope.

(** Complete address-8 precompile computation. The caller supplies the fork's
    base/per-pair prices; the interpreter frame supplies gas and status. *)
Module Bn254PairingRun.
  Module Fq12 := Bn254Tower.Fq12.

  Module Result.
    Inductive t : Set :=
    | Success (cost : Z) (output : list Z)
    | OutOfGas
    | InvalidLength
    | InvalidField
    | InvalidPoint.
  End Result.

  Fixpoint accumulate (pairs : nat) (input : list Z)
      (acc : Fq12.t) : Result.t :=
    match pairs with
    | O => Result.Success 0 (if Fq12.is_one acc ||
        Fq12.is_one (Bn254FinalExp.run acc)
      then List.repeat 0 31 ++ [1]
      else List.repeat 0 32)
    | S rest =>
      let g1_bytes := List.firstn 64 input in
      let g2_bytes := List.firstn 128 (List.skipn 64 input) in
      if negb (List.forallb Bn254Pairing.valid_byte g1_bytes) then
        Result.InvalidField else
      match Bn254.decode_point g1_bytes with
      | Bn254.Decoded.Invalid Bn254.Error.FieldPointNotAMember =>
          Result.InvalidField
      | Bn254.Decoded.Invalid Bn254.Error.AffineGFailedToCreate =>
          Result.InvalidPoint
      | Bn254.Decoded.Valid g1 =>
        match Bn254Pairing.decode_g2 g2_bytes with
        | Bn254Pairing.Decoded.Invalid Bn254Pairing.Error.InvalidLength =>
            Result.InvalidLength
        | Bn254Pairing.Decoded.Invalid Bn254Pairing.Error.FieldPointNotAMember =>
            Result.InvalidField
        | Bn254Pairing.Decoded.Invalid Bn254Pairing.Error.AffineGFailedToCreate =>
            Result.InvalidPoint
        | Bn254Pairing.Decoded.Valid g2 =>
          let rest_input := List.skipn 192 input in
          match Bn254.Point.to_affine g1 with
          | None => accumulate rest rest_input acc
          | Some (p_x, p_y) =>
            let next_acc := if Bn254Pairing.G2.is_infinity g2 then acc
              else Fq12.mul acc (Bn254Miller.run p_x p_y g2) in
            accumulate rest rest_input next_acc
          end
        end
      end
    end.

  Definition run (base_cost pair_cost : Z) (input : list Z)
      (gas_limit : Z) : Result.t :=
    let length := List.length input in
    let pair_count := Nat.div length 192 in
    let cost := base_cost + pair_cost * Z.of_nat pair_count in
    if gas_limit <? cost then Result.OutOfGas else
    if negb (Nat.eqb (Nat.modulo length 192) 0) then
      Result.InvalidLength else
    match accumulate pair_count input Fq12.one with
    | Result.Success _ output => Result.Success cost output
    | Result.OutOfGas => Result.OutOfGas
    | Result.InvalidLength => Result.InvalidLength
    | Result.InvalidField => Result.InvalidField
    | Result.InvalidPoint => Result.InvalidPoint
    end.
End Bn254PairingRun.
