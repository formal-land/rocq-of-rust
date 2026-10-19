From Stdlib Require Import Bool List.

Require Import p256.simulate.arithmetic.
Require Import p256.simulate.arithmetic.field.
Require Import simulate.RocqOfRust.

(** P256 specialization of primeorder/affine.rs. Only uncompressed nonidentity
    public keys are decoded here, matching the REVM provider's untagged input. *)
Module AffinePoint.
  Record t : Set := { x : FieldElement.t; y : FieldElement.t }.

  Definition from_encoded_point (input : list u8) : option t :=
    if negb (Nat.eqb (List.length input) 64) then None else
    match FieldElement.from_bytes (List.firstn 32 input),
      FieldElement.from_bytes (List.skipn 32 input) with
    | Some x, Some y =>
      let rhs := FieldElement.add
        (FieldElement.add (FieldElement.mul (FieldElement.square x) x)
          (FieldElement.mul NistP256.EQUATION_A x)) NistP256.EQUATION_B in
      if FieldElement.eq (FieldElement.square y) rhs
      then Some {| x := x; y := y |} else None
    | _, _ => None
    end.
End AffinePoint.
