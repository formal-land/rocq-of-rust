Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.links.cmp.
Require Import core.links.clone.
Require Import core.ops.range.

(*
  pub struct Range<Idx> {
      pub start: Idx,
      pub end: Idx,
  }
*)
Module Range.
  Record t {Idx : Set} : Set := {
    start : Idx;
    end_ : Idx;
  }.
  Arguments t : clear implicits.

  Global Instance IsLink (Idx : Set) `{Link Idx} : Link (t Idx) := {
    Φ :=
      Ty.apply (Ty.path "core::ops::range::Range") [] [ Φ Idx ];
    φ x :=
      Value.StructRecord "core::ops::range::Range" [] [ Φ Idx ] [
        ("end_", φ x.(end_));
        ("start", φ x.(start))
      ];
  }.

  Definition of_ty (Idx_ty : Ty.t) :
    OfTy.t Idx_ty ->
    OfTy.t (Ty.apply (Ty.path "core::ops::range::Range") [] [ Idx_ty ]).
  Proof.
    intros [Idx].
    eapply OfTy.Make with (A := t Idx).
    subst.
    reflexivity.
  Defined.
  Smpl Add eapply of_ty : of_ty.

  Lemma of_value_with {Idx : Set} `{Link Idx} Idx'
      (start : Idx) start'
      (end_ : Idx) end_' :
    Idx' = Φ Idx ->
    start' = φ start ->
    end_' = φ end_ ->
    Value.StructRecord "core::ops::range::Range" [] [Idx'] [
      ("end_", end_');
      ("start", start')
    ] =
    φ (Build_t Idx start end_).
  Proof. now intros; subst. Qed.
  Smpl Add eapply of_value_with : of_value.

  Definition of_value Idx' start' end_'
      (H_Idx : OfTy.t Idx')
      (start end_ : OfTy.get_Set H_Idx) :
    start' = φ start ->
    end_' = φ end_ ->
    OfValue.t (Value.StructRecord "core::ops::range::Range" [] [Idx'] [
      ("end_", end_');
      ("start", start')
    ]).
  Proof.
    intros.
    destruct H_Idx as [Idx].
    eapply OfValue.Make with (A := t Idx) (value := Build_t Idx start end_).
    now subst.
  Defined.
  Smpl Add unshelve eapply of_value : of_value.
End Range.

Module Impl_Clone_for_Range.
  Definition Self (Idx : Set) : Set :=
    Range.t Idx.

  Instance run (Idx : Set) `{Link Idx} : Clone.Run (Self Idx).
  Admitted.
End Impl_Clone_for_Range.
Export Impl_Clone_for_Range.

Module Impl_Range.
  Definition Self (Idx : Set) : Set :=
    Range.t Idx.

  (* pub fn is_empty(&self) -> bool *)
  Instance run_is_empty {Idx : Set} `{Link Idx} (self : '& (Self Idx)) :
    Run.Trait
      (ops.range.Impl_core_ops_range_Range_Idx.is_empty (Φ Idx)) [] [] [ φ self ]
      bool.
  Admitted.
  Global Opaque run_is_empty.
End Impl_Range.
Export Impl_Range.

(*
  pub enum Bound<T> {
    Included(T),
    Excluded(T),
    Unbounded,
  }
*)
Module Bound.
  Inductive t {T : Set} : Set :=
  | Included : T -> t
  | Excluded : T -> t
  | Unbounded : t.
  Arguments t : clear implicits.

  Global Instance IsLink {T : Set} `{Link T} : Link (t T) := {
    Φ := Ty.apply (Ty.path "core::ops::Range::Bound") [] [Φ T];
    φ x :=
      match x with
      | Included x => Value.StructTuple "core::ops::Range::Bound::Included" [] [Φ T] [φ x]
      | Excluded x => Value.StructTuple "core::ops::Range::Bound::Excluded" [] [Φ T] [φ x]
      | Unbounded => Value.StructTuple "core::ops::Range::Bound::Unbounded" [] [Φ T] []
      end;
  }.
End Bound.

(*
  pub trait RangeBounds<T: ?Sized> {
    fn start_bound(&self) -> Bound<&T>;
    fn end_bound(&self) -> Bound<&T>;
    fn contains<U>(&self, item: &U) -> bool
    where
        T: PartialOrd<U>,
        U: ?Sized + PartialOrd<T>
    fn is_empty(&self) -> bool
    where
        T: PartialOrd;
  }
*)
Module RangeBounds.
  Definition trait (Self T : Set) `{Link Self} `{Link T} : TraitMethod.Header.t :=
    ("core::ops::RangeBounds", [], [Φ T], Φ Self).

  Definition Run_start_bound (Self : Set) `{Link Self} 
      (T : Set) `{Link T} : Set :=
    {start_bound @
      IsTraitMethod.t "core::ops::RangeBounds" [] [] (Φ Self) "start_bound" start_bound *
      forall (self : '& Self),
        {{ start_bound [] [] [φ self] 🔽 Bound.t ('& T) }}
    }.

  Definition Run_end_bound (Self : Set) `{Link Self} 
      (T : Set) `{Link T} : Set :=
    {end_bound @
      IsTraitMethod.t "core::ops::RangeBounds" [] [] (Φ Self) "end_bound" end_bound *
      forall (self : '& Self),
        {{ end_bound [] [] [φ self] 🔽 Bound.t ('& T) }}
    }.

  Definition Run_contains (Self : Set) `{Link Self} 
      (T : Set) `{Link T}  : Set :=
    {contains @
      IsTraitMethod.t "core::ops::RangeBounds" [] [] (Φ Self) "contains" contains *
      forall 
          (self : '& Self)
          (U : Set) `(Link U)
          (item : '& U)
          (run_Ord_for_T : PartialOrd.Run T T)
          (run_Ord_for_U : PartialOrd.Run U U),
        {{ contains [] [] [φ self; φ item] 🔽 bool }}
    }.

  Definition Run_is_empty (Self : Set) `{Link Self} 
      (T : Set) `{Link T} : Set :=
    {is_empty @ 
      IsTraitMethod.t "core::ops::RangeBounds" [] [] (Φ Self) "is_empty" is_empty *
      forall (self : '& Self)
          (run_Ord_for_T : PartialOrd.Run T T),
        {{ is_empty [] [] [φ self] 🔽 bool }}
    }.

  Record Run (Self : Set) `{Link Self} 
      {T : Set} `{Link T} : Set := {
    start_bound : Run_start_bound Self T;
    end_bound : Run_end_bound Self T;
    contains : Run_contains Self T;
    is_empty : Run_is_empty Self T;
  }.
End RangeBounds.
Export RangeBounds.

(*
pub struct RangeTo<Idx> {
    pub end: Idx,
}
*)
Module RangeTo.
  Record t {Idx : Set} : Set := {
    end_ : Idx;
  }.
  Arguments t : clear implicits.

  Global Instance IsLink (Idx : Set) `{Link Idx} : Link (t Idx) := {
    Φ := Ty.apply (Ty.path "core::ops::range::RangeTo") [] [Φ Idx];
    φ x := Value.StructRecord "core::ops::range::RangeTo" [] [Φ Idx] [("end_", φ x.(end_))];
  }.

  Definition of_ty (Idx_ty : Ty.t) :
    OfTy.t Idx_ty ->
    OfTy.t (Ty.apply (Ty.path "core::ops::range::RangeTo") [] [ Idx_ty ]).
  Proof.
    intros [Idx].
    eapply OfTy.Make with (A := t Idx).
    subst.
    reflexivity.
  Defined.
  Smpl Add eapply of_ty : of_ty.

  Lemma of_value_with {Idx : Set} `{Link Idx} Idx' (end_ : Idx) end_' :
    Idx' = Φ Idx ->
    end_' = φ end_ ->
    Value.StructRecord "core::ops::range::RangeTo" [] [Idx'] [("end_", end_')] =
    φ (Build_t Idx end_).
  Proof.
    now intros; subst.
  Qed.
  Smpl Add eapply of_value_with : of_value.

  Definition of_value Idx' end_' :
    forall
      (of_value_end : OfValue.t end_'),
    Idx' = Φ (OfValue.get_Set of_value_end) ->
    OfValue.t (Value.StructRecord "core::ops::range::RangeTo" [] [Idx'] [("end_", end_')]).
  Proof.
    intros [Idx ? end_] **.
    eapply OfValue.Make with (A := t Idx) (value := Build_t Idx end_).
    now subst.
  Defined.
  Smpl Add unshelve eapply of_value : of_value.
End RangeTo.
Export RangeTo.
