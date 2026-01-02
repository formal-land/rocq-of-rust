Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.fmt.rt.
Require Import core.links.array.

(*
pub struct Argument<'a> {
    ty: ArgumentType<'a>,
}
*)
Module Argument.
  Parameter t : Set.

  Parameter to_value : t -> Value.t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "core::fmt::rt::Argument";
    φ := to_value;
  }.

  Definition of_ty : OfTy.t (Ty.path "core::fmt::rt::Argument").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End Argument.

Module Impl_Argument.
  Definition Self : Set :=
    Argument.t.

  (* pub const fn new_display<T: Display>(x: &T) -> Argument<'_> *)
  Instance run_new_display (T : Set) `{Link T} (x : Ref.t Pointer.Kind.Ref T) :
    Run.Trait fmt.rt.Impl_core_fmt_rt_Argument.new_display [] [Φ T] [φ x] Self.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_new_display.

  (* pub fn none() -> [Self; 0] *)
  Instance run_none :
    Run.Trait fmt.rt.Impl_core_fmt_rt_Argument.none [] [] [] (array.t Self {| Integer.value := 0 |}).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_none.
End Impl_Argument.
Export Impl_Argument.
