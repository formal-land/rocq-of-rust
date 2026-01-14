Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.fmt.links.rt.
Require Import core.fmt.mod.
Require Import core.links.array.

(*
pub struct Arguments<'a> {
    pieces: &'a [&'static str],
    fmt: Option<&'a [rt::Placeholder]>,
    args: &'a [rt::Argument<'a>],
}
*)
Module Arguments.
  Parameter t : Set.

  Parameter to_value : t -> Value.t.

  Instance IsLink : Link t := {
    Φ := Ty.path "core::fmt::Arguments";
    φ := to_value;
  }.

  Definition of_ty : OfTy.t (Ty.path "core::fmt::Arguments").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End Arguments.
Export (hints) Arguments.

Module Impl_Arguments.
  Definition Self : Set := Arguments.t.

  (* pub const fn new_const<const N: usize>(pieces: &'a [&'static str; N]) -> Self *)
  Instance run_new_const
      (N : usize)
      (pieces : '& (array.t ('& string) N)) :
    Run.Trait fmt.Impl_core_fmt_Arguments.new_const [φ N] [] [φ pieces] Self.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_new_const.

  (*
    pub fn new_v1<const P: usize, const A: usize>(
        pieces: &'a [&'static str; P],
        args: &'a [rt::Argument<'a>; A],
    ) -> Arguments<'a>
  *)
  Instance run_new_v1
      (P A : usize)
      (pieces : '& (array.t ('& string) P))
      (args : '& (array.t Argument.t A)) :
    Run.Trait fmt.Impl_core_fmt_Arguments.new_v1 [φ P; φ A] [] [φ pieces; φ args] Self.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_new_v1.
End Impl_Arguments.
Export (hints) Impl_Arguments.
