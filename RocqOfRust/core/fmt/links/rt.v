Require Import links.RocqOfRust.
Require Import core.fmt.rt.

(*
pub struct Argument<'a> {
    ty: ArgumentType<'a>,
}
*)
Module Argument.
  Parameter t : Set.

  Parameter to_value : t -> Value.t.

  Instance IsLink : Link t := {
    Φ := Ty.path "core::fmt::rt::Argument";
    φ := to_value;
  }.

  Definition of_ty : OfTy.t (Ty.path "core::fmt::rt::Argument").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End Argument.
Export (hints) Argument.

Module Impl_Argument.
  Definition Self : Set :=
    Argument.t.

  (* pub const fn new_display<T: Display>(x: &T) -> Argument<'_> *)
  Instance run_new_display (T : Set) `{Link T} (x : '& T) :
    Run.Trait fmt.rt.Impl_core_fmt_rt_Argument.new_display [] [Φ T] [φ x] Self.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_new_display.

End Impl_Argument.
Export (hints) Impl_Argument.
