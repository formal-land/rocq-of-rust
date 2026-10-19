From Stdlib Require Import Bool List.

Require Import p256.simulate.arithmetic.scalar.
Require Import simulate.RocqOfRust.

(** P256 specialization of ecdsa/lib.rs signature parsing. *)
Module Signature.
  Record t : Set := { r : Scalar.t; s : Scalar.t }.

  Definition from_slice (input : list u8) : option t :=
    if negb (Nat.eqb (List.length input) 64) then None else
    match Scalar.from_bytes (List.firstn 32 input), Scalar.from_bytes (List.skipn 32 input) with
    | Some r, Some s =>
      if Scalar.is_zero r || Scalar.is_zero s then None else Some {| r := r; s := s |}
    | _, _ => None
    end.
End Signature.
