Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.convert.links.mod.
Require Import core.fmt.links.mod.
Require Import core.fmt.links.rt.
Require Import core.links.panicking.
Require Import core.links.result.
Require Import core.num.links.error.
Require Import ruint.links.lib.
Require Import ruint.from.

(*
  pub enum ToUintError<T> {
      ValueTooLarge(usize, T),
      ValueNegative(usize, T),
      NotANumber(usize),
  }
*)
Module ToUintError.
  Inductive t (T : Set) : Set :=
  | ValueTooLarge (size : Usize.t) (value : T)
  | ValueNegative (size : Usize.t) (value : T)
  | NotANumber (size : Usize.t)
  .
  Arguments ValueTooLarge {T} size value.
  Arguments ValueNegative {T} size value.
  Arguments NotANumber {T} size.

  Global Instance IsLink (T : Set) `{Link T} : Link (t T) :=
  {
    Φ := Ty.apply (Ty.path "ruint::from::ToUintError") [] [ Φ T ];
    φ x :=
      match x with
      | ValueTooLarge size value => Value.StructTuple "ruint::from::ToUintError::ValueTooLarge" [] [ Φ Usize.t; Φ T ] [ φ size; φ value ]
      | ValueNegative size value => Value.StructTuple "ruint::from::ToUintError::ValueNegative" [] [ Φ Usize.t; Φ T ] [ φ size; φ value ]
      | NotANumber size => Value.StructTuple "ruint::from::ToUintError::NotANumber" [] [ Φ Usize.t ] [ φ size ]
      end
  }.

  Definition of_ty (T_ty : Ty.t) :
    OfTy.t T_ty ->
    OfTy.t (Ty.apply (Ty.path "ruint::from::ToUintError") [] [ T_ty ]).
  Proof.
    intros [T].
    eapply OfTy.Make with (A := t T).
    subst.
    reflexivity.
  Defined.
  Smpl Add eapply of_ty : of_ty.
End ToUintError.
Export ToUintError.

(*
  pub trait UintTryFrom<T>: Sized {
      #[doc(hidden)]
      fn uint_try_from(value: T) -> Result<Self, ToUintError<Self>>;
  }
*)
Module UintTryFrom.
  Definition trait (Self T : Set) `{Link Self} `{Link T} : TraitMethod.Header.t :=
    ("ruint::from::UintTryFrom", [], [Φ T], Φ Self).

  Definition Run_uint_try_from (Self T : Set) `{Link Self} `{Link T} : Set :=
    TraitMethod.C (trait Self T) "uint_try_from" (fun method =>
      forall (value : T),
      Run.Trait method [] [] [ φ value ] (Result.t Self (ToUintError.t Self))
    ).

  Class Run (Self : Set) (T : Set) `{Link Self} `{Link T} : Set := {
    run_uint_try_from : Run_uint_try_from Self T;
  }.
End UintTryFrom.

(*
  impl<const BITS: usize, const LIMBS: usize, T> UintTryFrom<T> for Uint<BITS, LIMBS>
  where
      Self: TryFrom<T, Error = ToUintError<Self>>,
*)
Module UintTryFrom_T_for_Uint_where_TryFrom.
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  Instance run_uint_try_from {BITS LIMBS : Usize.t} {T : Set} `{Link T}
      {run_TryFrom_for_Self : TryFrom.Run (Self BITS LIMBS) T (ToUintError.t (Self BITS LIMBS))}
      (value : T) :
    Trait
      (from.Impl_ruint_from_UintTryFrom_where_core_convert_TryFrom_ruint_Uint_BITS_LIMBS_T_T_for_ruint_Uint_BITS_LIMBS.uint_try_from (φ BITS) (φ LIMBS) (Φ T))
      [] [] [φ value]
      (Result.t (Self BITS LIMBS) (ToUintError.t (Self BITS LIMBS))).
  Proof.
    constructor.
    destruct run_TryFrom_for_Self.
    run_symbolic.
  Qed.
  Global Opaque run_uint_try_from.

  Definition Run_uint_try_from {BITS LIMBS : Usize.t} {T : Set} `{Link T}
      `{!TryFrom.Run (Self BITS LIMBS) T (ToUintError.t (Self BITS LIMBS))} :
    UintTryFrom.Run_uint_try_from (Self BITS LIMBS) T.
  Proof.
    econstructor.
    { eapply IsTraitMethod.Defined.
      { apply from.Impl_ruint_from_UintTryFrom_where_core_convert_TryFrom_ruint_Uint_BITS_LIMBS_T_T_for_ruint_Uint_BITS_LIMBS.Implements. }
      { reflexivity. }
    }
    { apply run_uint_try_from. }
  Defined.

  Instance run (BITS LIMBS : Usize.t) (T : Set) `{Link T}
      `{!TryFrom.Run (Self BITS LIMBS) T (ToUintError.t (Self BITS LIMBS))} :
    UintTryFrom.Run (Self BITS LIMBS) T :=
  {
    UintTryFrom.run_uint_try_from := Run_uint_try_from;
  }.
End UintTryFrom_T_for_Uint_where_TryFrom.
Export (hints) UintTryFrom_T_for_Uint_where_TryFrom.

(* impl<const BITS: usize, const LIMBS: usize> TryFrom<u64> for Uint<BITS, LIMBS> *)
Module TryFrom_u64_for_Uint.
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  Definition Error (BITS LIMBS : Usize.t) : Set :=
    ToUintError.t (Self BITS LIMBS).

  Lemma Error_IsAssociated (BITS LIMBS : Usize.t) :
    IsTraitAssociatedType
      "core::convert::TryFrom" [] [Φ U64.t] (Φ (Self BITS LIMBS)) "Error"
      (Φ (Error BITS LIMBS)).
  Proof.
    eexists; split.
    { apply from.Impl_core_convert_TryFrom_u64_for_ruint_Uint_BITS_LIMBS.Implements. }
    { reflexivity. }
  Qed.

  Instance run_try_from (BITS LIMBS : Usize.t) (value : U64.t) :
    Run.Trait
      (from.Impl_core_convert_TryFrom_u64_for_ruint_Uint_BITS_LIMBS.try_from (φ BITS) (φ LIMBS))
      [] [] [ φ value ]
      (Result.t (Self BITS LIMBS) (ToUintError.t (Self BITS LIMBS))).
  Proof.
    constructor.
    pose proof Error_IsAssociated.
    run_symbolic.
    all: cbn.
  Admitted.
  Global Opaque run_try_from.

  Definition Run_try_from {BITS LIMBS : Usize.t} :
    TryFrom.Run_try_from (Self BITS LIMBS) U64.t (Error BITS LIMBS).
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply from.Impl_core_convert_TryFrom_u64_for_ruint_Uint_BITS_LIMBS.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance Run (BITS LIMBS : Usize.t) :
    TryFrom.Run (Self BITS LIMBS) U64.t (Error BITS LIMBS) :=
  {
    TryFrom.try_from := Run_try_from;
  }.
End TryFrom_u64_for_Uint.
Export (hints) TryFrom_u64_for_Uint.

(* impl_from_unsigned_int!(bool); *)
Module TryFrom_bool_for_Uint.
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  Definition Error (BITS LIMBS : Usize.t) : Set :=
    ToUintError.t (Self BITS LIMBS).

  Instance run_try_from (BITS LIMBS : Usize.t) (value : bool) :
    Run.Trait
      (from.Impl_core_convert_TryFrom_bool_for_ruint_Uint_BITS_LIMBS.try_from (φ BITS) (φ LIMBS))
      [] [] [ φ value ]
      (Result.t (Self BITS LIMBS) (ToUintError.t (Self BITS LIMBS))).
  Proof.
    constructor.
    destruct (TryFrom_u64_for_Uint.Run BITS LIMBS).
    run_symbolic.
  Defined.
  Global Opaque run_try_from.

  Definition Run_try_from {BITS LIMBS : Usize.t} :
    TryFrom.Run_try_from (Self BITS LIMBS) bool (Error BITS LIMBS).
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply from.Impl_core_convert_TryFrom_bool_for_ruint_Uint_BITS_LIMBS.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance Run (BITS LIMBS : Usize.t) :
    TryFrom.Run (Self BITS LIMBS) bool (Error BITS LIMBS) :=
  {
    TryFrom.try_from := Run_try_from;
  }.
End TryFrom_bool_for_Uint.
Export (hints) TryFrom_bool_for_Uint.

Module Impl_Uint.
  (* Uint<BITS, LIMBS> *)
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  (* 
  pub fn from<T>(value: T) -> Self
        where
            Self: UintTryFrom<T>,
  *)
  Instance run_from
    (BITS LIMBS : Usize.t)
    (T : Set) `{Link T}
    (* {run_UintTryFrom_for_Self : UintTryFrom.Run (Self BITS LIMBS) T} *)
    (value : T) :
    Run.Trait
      (from.Impl_ruint_Uint_BITS_LIMBS.from (φ BITS) (φ LIMBS)) [] [ Φ T ] [ φ value ]
      (Self BITS LIMBS).
  Proof.
    constructor.
    (* destruct run_UintTryFrom_for_Self. *)
    run_symbolic.
  (* Defined. *)
  Admitted.
  Global Opaque run_from.
End Impl_Uint.
Export (hints) Impl_Uint.

(*
pub enum FromUintError<T> {
    Overflow(usize, T, T),
}
*)
Module FromUintError.
  Parameter t : forall (T : Set), Set.

  Parameter to_value : forall {T : Set}, t T -> Value.t.

  Global Instance IsLink (T : Set) `{Link T} : Link (t T) :=
  {
    Φ := Ty.apply (Ty.path "ruint::from::FromUintError") [] [ Φ T ];
    φ := to_value;
  }.

  Definition of_ty (T_ty : Ty.t) :
    OfTy.t T_ty ->
    OfTy.t (Ty.apply (Ty.path "ruint::from::FromUintError") [] [ T_ty ]).
  Proof.
    intros [T].
    eapply OfTy.Make with (A := t T).
    subst.
    reflexivity.
  Defined.
  Smpl Add eapply of_ty : of_ty.
End FromUintError.

Module TryFrom_Uint_for_u64.
  Definition Self : Set :=
    U64.t.

  Instance run_try_from (BITS LIMBS : Usize.t) (value : Impl_Uint.Self BITS LIMBS) :
    Run.Trait
      (from.Impl_core_convert_TryFrom_ruint_Uint_BITS_LIMBS_for_u64.try_from (φ BITS) (φ LIMBS))
      [] [] [ φ value ]
      (Result.t Self (FromUintError.t U64.t)).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_try_from.

  Definition Run_try_from (BITS LIMBS : Usize.t) :
    TryFrom.Run_try_from Self (Impl_Uint.Self BITS LIMBS) (FromUintError.t U64.t).
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply from.Impl_core_convert_TryFrom_ruint_Uint_BITS_LIMBS_for_u64.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run (BITS LIMBS : Usize.t) :
    TryFrom.Run Self (Impl_Uint.Self BITS LIMBS) (FromUintError.t U64.t) :=
  {
    TryFrom.try_from := Run_try_from BITS LIMBS;
  }.
End TryFrom_Uint_for_u64.
Export (hints) TryFrom_Uint_for_u64.
