Require Import links.RocqOfRust.
Require Import core.convert.mod.
Require Import core.links.result.

Require Export core.convert.links.mod_Infaillible.

(*
pub trait From<T>: Sized {
    fn from(value: T) -> Self;
}
*)
Module From.
  Definition trait (Self T : Set) `{Link Self} `{Link T} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::convert::From";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [Φ T];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_from (Self T : Set) `{Link Self} `{Link T} : Set := {
    from : PolymorphicFunction.t;
    from_is_method :: IsTraitMethod.C (trait Self T) "from" from;
    run_from (value : T) :: Run.Trait from [] [] [ φ value ] Self;
  }.

  Class Run (Self : Set) (T : Set) `{Link Self} `{Link T} : Set := {
    method_from :: Method_from Self T;
  }.
End From.
Export (hints) From.

(* impl<T> From<T> for T *)
Module Impl_From_for_T.
  Instance run
    (T : Set) `{Link T} :
    From.Run T T.
  Proof.
  Admitted.
End Impl_From_for_T.
Export (hints) Impl_From_for_T.

(*
pub trait Into<T>: Sized {
    fn into(self) -> T;
}
*)
Module Into.
  Definition trait (Self T : Set) `{Link Self} `{Link T} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::convert::Into";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [Φ T];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_into (Self T : Set) `{Link Self} `{Link T} : Set := {
    into : PolymorphicFunction.t;
    into_is_method :: IsTraitMethod.C (trait Self T) "into" into;
    run_into (self : Self) :: Run.Trait into [] [] [ φ self ] T;
  }.

  Class Run (Self : Set) (T : Set) `{Link Self} `{Link T} : Set := {
    method_into :: Method_into Self T;
  }.
End Into.
Export (hints) Into.

(*
impl<T, U> Into<U> for T
where
    U: From<T>,
*)
Module Impl_Into_for_From_T.
  Instance run_into (T U : Set) `{Link T} `{Link U} `{!From.Run U T} (value : T) :
    Run.Trait
      (convert.Impl_core_convert_Into_where_core_convert_From_U_T_U_for_T.into (Φ T) (Φ U))
      [] [] [φ value] U.
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_into.

  Instance method_into
    (T U : Set) `{Link T} `{Link U}
    `(!From.Run U T) :
    Into.Method_into T U.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply convert.Impl_core_convert_Into_where_core_convert_From_U_T_U_for_T.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run
    {T U : Set} `{Link T} `{Link U}
    `(!From.Run U T) :
    Into.Run T U :=
  {}.
End Impl_Into_for_From_T.
Export (hints) Impl_Into_for_From_T.

(*
pub trait AsRef<T: ?Sized> {
    fn as_ref(&self) -> &T;
}
*)
Module AsRef.
  Definition trait (Self T : Set) `{Link Self} `{Link T} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::convert::AsRef";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [Φ T];
      TraitHeader.self_ty := Φ Self;
    |}.


  Class Method_as_ref (Self T : Set) `{Link Self} `{Link T} : Set := {
    as_ref : PolymorphicFunction.t;
    as_ref_is_method :: IsTraitMethod.C (trait Self T) "as_ref" as_ref;
    run_as_ref (self : '& Self) :: Run.Trait as_ref [] [] [ φ self ] ('& T);
  }.

  Class Run (Self : Set) (T : Set) `{Link Self} `{Link T} : Set := {
    method_as_ref :: Method_as_ref Self T;
  }.
End AsRef.
Export (hints) AsRef.

(* impl<T> AsRef<[T]> for [T] *)
Module Impl_AsRef_for_Slice.
  Definition Self (T : Set) : Set :=
    list T.

  Instance run_as_ref (T : Set) `{Link T} (self : '& (Self T)) :
    Run.Trait (convert.Impl_core_convert_AsRef_slice_T_for_slice_T.as_ref (Φ T))
      [] [] [φ self]
      ('& (list T)).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_as_ref.

  Instance method_as_ref
    (T : Set) `{Link T} :
    AsRef.Method_as_ref (Self T) (list T).
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply convert.Impl_core_convert_AsRef_slice_T_for_slice_T.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run
    (T : Set) `{Link T} :
    AsRef.Run (list T) (list T) :=
  {}.
End Impl_AsRef_for_Slice.
Export (hints) Impl_AsRef_for_Slice.

(*
impl<T: PointeeSized, U: PointeeSized> const AsRef<U> for &T
where
    T: [const] AsRef<U>
*)
Module Impl_AsRef_for_Ref.
  Definition Self (T : Set) `{Link T} : Set :=
    '& T.

  Instance run_as_ref (T U : Set) `{Link T} `{Link U} (self : '& (Self T))
      `{!AsRef.Run T U} :
    Run.Trait (convert.Impl_core_convert_AsRef_where_core_marker_PointeeSized_T_where_core_marker_PointeeSized_U_where_core_convert_AsRef_T_U_U_for_ref__T.as_ref (Φ T) (Φ U))
      [] [] [φ self]
      ('& U).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_as_ref.

  Instance method_as_ref
    (T U : Set) `{Link T} `{Link U}
    `{!AsRef.Run T U} :
    AsRef.Method_as_ref (Self T) U.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply convert.Impl_core_convert_AsRef_where_core_marker_PointeeSized_T_where_core_marker_PointeeSized_U_where_core_convert_AsRef_T_U_U_for_ref__T.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run
    (T U : Set) `{Link T} `{Link U}
    `{!AsRef.Run T U} :
    AsRef.Run (Self T) U :=
  {}.
End Impl_AsRef_for_Ref.
Export (hints) Impl_AsRef_for_Ref.

(*
pub trait TryFrom<T>: Sized {
    type Error;
    fn try_from(value: T) -> Result<Self, Self::Error>;
}
*)
Module TryFrom.
  Definition trait (Self T : Set) `{Link Self} `{Link T} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::convert::TryFrom";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [Φ T];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_try_from (Self T Error : Set) `{Link Self} `{Link T} `{Link Error} : Set := {
    try_from : PolymorphicFunction.t;
    try_from_is_method :: IsTraitMethod.C (trait Self T) "try_from" try_from;
    run_try_from (value : T) :: Run.Trait try_from [] [] [ φ value ] (Result.t Self Error);
  }.

  Class Run (Self : Set) (T : Set) (Error : Set) `{Link Self} `{Link T} `{Link Error} : Set := {
    method_try_from :: Method_try_from Self T Error;
  }.
End TryFrom.
Export (hints) TryFrom.

(*
pub trait TryInto<T>: Sized {
    type Error;

    fn try_into(self) -> Result<T, Self::Error>;
}
*)
Module TryInto.
  Definition trait (Self T : Set) `{Link Self} `{Link T} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::convert::TryInto";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [Φ T];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_try_into (Self T Error : Set) `{Link Self} `{Link T} `{Link Error} : Set := {
    try_into : PolymorphicFunction.t;
    try_into_is_method :: IsTraitMethod.C (trait Self T) "try_into" try_into;
    run_try_into (self : Self) :: Run.Trait try_into [] [] [ φ self ] (Result.t T Error);
  }.

  Class Run (Self : Set) (T : Set) (Error : Set) `{Link Self} `{Link T} `{Link Error} : Set := {
    method_try_into :: Method_try_into Self T Error;
  }.
End TryInto.
Export (hints) TryInto.

(*
impl<T, U> TryInto<U> for T
where
    U: TryFrom<T>,
{
    type Error = U::Error;
*)
Module Impl_TryInto_for_TryFrom_T.
  Instance run
    (T U Error : Set) `{Link T} `{Link U} `{Link Error}
    {run_TryFrom_for_U : TryFrom.Run U T Error} :
    TryInto.Run T U Error.
  Proof.
  Admitted.
End Impl_TryInto_for_TryFrom_T.
Export (hints) Impl_TryInto_for_TryFrom_T.
