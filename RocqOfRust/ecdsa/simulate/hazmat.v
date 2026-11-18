Require Import ecdsa.simulate.lib.
Require Import p256.simulate.arithmetic.field.
Require Import p256.simulate.arithmetic.scalar.
Require Import primeorder.simulate.affine.
Require Import primeorder.simulate.projective.
Require Import simulate.RocqOfRust.

(** P256 specialization of ecdsa/hazmat.rs verification. This follows the
    scalar reduction, inverse and linear-combination sequence of Rust. *)
Module hazmat.
  Definition verify_prehashed (key : ProjectivePoint.t) (message : list u8)
      (signature : Signature.t) : option unit :=
    match Scalar.reduce_bytes message, Scalar.invert signature.(Signature.s) with
    | Some z, Some inverse =>
      let u1 := Scalar.mul z inverse in
      let u2 := Scalar.mul signature.(Signature.r) inverse in
      match ProjectivePoint.to_affine
        (ProjectivePoint.lincomb ProjectivePoint.GENERATOR u1 key u2) with
      | None => None
      | Some result =>
        if Scalar.eq signature.(Signature.r)
          (Scalar.reduce result.(AffinePoint.x).(FieldElement.repr))
        then Some tt else None
      end
    | _, _ => None
    end.
End hazmat.
