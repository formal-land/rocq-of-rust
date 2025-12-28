Require Import RocqOfRust.RocqOfRust.
Require Import links.M.
Require Import core.convert.mod.

(* pub enum Infallible {} *)
Module Infallible.
  Inductive t : Set :=.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "core::convert::Infallible";
    φ x := match x with end;
  }.

  Definition of_ty : OfTy.t (Ty.path "core::convert::Infallible").
  Proof.
    eapply OfTy.Make.
    subst; reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.
End Infallible.
