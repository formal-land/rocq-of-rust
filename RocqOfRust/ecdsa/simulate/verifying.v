Require Import ecdsa.simulate.hazmat.
Require Import ecdsa.simulate.lib.
Require Import primeorder.simulate.affine.
Require Import primeorder.simulate.projective.
Require Import simulate.RocqOfRust.

(** P256 specialization of ecdsa/verifying.rs. High-s signatures are accepted,
    matching Rust's P256 verifier rather than transaction recovery. *)
Module VerifyingKey.
  Definition t : Set := AffinePoint.t.

  Definition from_encoded_point := AffinePoint.from_encoded_point.

  Definition verify_prehash (key : t) (message : list u8) (signature : Signature.t)
      : option unit :=
    hazmat.verify_prehashed (ProjectivePoint.from_affine key) message signature.
End VerifyingKey.
