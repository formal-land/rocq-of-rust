Require Import links.RocqOfRust.
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

  (* pub unsafe fn new<const N: usize, const M: usize>(
      template: &'a [u8; N],
      args: &'a [rt::Argument<'a>; M],
  ) -> Arguments<'a> *)
  Instance run_new (N M : usize)
      (template : '& (array.t u8 N))
      (args : '& (array.t Argument.t M)) :
    Run.Trait fmt.Impl_core_fmt_Arguments.new [φ N; φ M] [] [φ template; φ args] Self.
  Proof.
  Admitted.
  Global Opaque run_new.

  Instance run_new_byte_str (N M : usize) (bytes : list Z)
      (args : '& (array.t Argument.t M)) :
    Run.Trait
      fmt.Impl_core_fmt_Arguments.new
      [φ N; φ M]
      []
      [
        M.mk_byte_str_ref N.(Integer.value) bytes;
        φ args
      ]
      Self.
  Proof.
    replace (M.mk_byte_str_ref N.(Integer.value) bytes) with (
      φ (Ref.immediate Pointer.Kind.Ref
        (array.Build_t u8 N
          (array.byte_string_array_pairs (Z.to_nat N.(Integer.value)) bytes)))
    ).
    { apply run_new. }
    unfold M.mk_byte_str_ref.
    symmetry.
    change (
      Value.Pointer {|
        Pointer.kind := Pointer.Kind.Ref;
        Pointer.core := Pointer.Core.Immediate (Some (
          Value.Array (M.byte_string_to_values (Z.to_nat N.(Integer.value)) bytes)
        ));
      |} =
      Value.Pointer {|
        Pointer.kind := Pointer.Kind.Ref;
        Pointer.core := Pointer.Core.Immediate (Some (
          Value.Array (array.ArrayPairs.to_values
            (array.byte_string_array_pairs (Z.to_nat N.(Integer.value)) bytes))
        ));
      |}
    ).
    now rewrite array.byte_string_to_values_eq.
  Defined.
  Global Opaque run_new_byte_str.

  (* pub const fn from_str(s: &'static str) -> Arguments<'a> *)
  Instance run_from_str (s : '& string) :
    Run.Trait fmt.Impl_core_fmt_Arguments.from_str [] [] [φ s] Self.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_from_str.

  (* pub fn from_str_nonconst(s: &'static str) -> Arguments<'a> *)
  Instance run_from_str_nonconst (s : '& string) :
    Run.Trait fmt.Impl_core_fmt_Arguments.from_str_nonconst [] [] [φ s] Self.
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_from_str_nonconst.
End Impl_Arguments.
Export (hints) Impl_Arguments.
