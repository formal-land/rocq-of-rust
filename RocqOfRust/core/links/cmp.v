Require Import links.RocqOfRust.
Require Import core.cmp.
Require Import core.intrinsics.links.mod.
Require Import core.links.option.
Require Import core.ops.links.function.
Require Export core.links.cmpOrdering.
Require Import core.links.array.

(*
pub trait PartialEq<Rhs: ?Sized = Self> {
    fn eq(&self, other: &Rhs) -> bool;
    fn ne(&self, other: &Rhs) -> bool;
}
*)
Module PartialEq.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::cmp::PartialEq";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [ Φ Rhs ];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_eq (Self Rhs : Set) `{Link Self} `{Link Rhs} : Set := {
    eq : PolymorphicFunction.t;
    eq_is_method :: IsTraitMethod.C (trait Self Rhs) "eq" eq;
    run_eq (self : '& Self) (other : '& Rhs) :: Run.Trait eq [] [] [ φ self; φ other ] bool;
  }.

  Class Method_ne (Self Rhs : Set) `{Link Self} `{Link Rhs} : Set := {
    ne : PolymorphicFunction.t;
    ne_is_method :: IsTraitMethod.C (trait Self Rhs) "ne" ne;
    run_ne (self : '& Self) (other : '& Rhs) :: Run.Trait ne [] [] [ φ self; φ other ] bool;
  }.

  Class Run (Self Rhs : Set) `{Link Self} `{Link Rhs} : Set := {
    method_eq :: Method_eq Self Rhs;
    method_ne :: Method_ne Self Rhs;
  }.
End PartialEq.
Export (hints) PartialEq.

(* pub trait Eq: PartialEq { } *)
Module Eq.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::cmp::Eq";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Run (Self : Set) `{Link Self} : Set := {
    run_PartialEq_for_Eq :: PartialEq.Run Self Self;
  }.
End Eq.
Export (hints) Eq.

Instance run_min_by {T F : Set} `{Link T} `{Link F}
    `{run_FnOnce_for_F : !FnOnce.Run F ('& T * '& T) Ordering.t}
    (v1 v2 : T) (compare : F) :
  Run.Trait cmp.min_by [] [ Φ T; Φ F ] [ φ v1; φ v2; φ compare ] T.
Proof.
  constructor.
  destruct run_FnOnce_for_F.
  run_symbolic.
Defined.
Global Opaque run_min_by.

(*
    pub fn max_by<T, F: FnOnce(&T, &T) -> Ordering>(v1: T, v2: T, compare: F) -> T {
        match compare(&v1, &v2) {
            Ordering::Less | Ordering::Equal => v2,
            Ordering::Greater => v1,
        }
    }
*)
Instance run_max_by {T F : Set} `{Link T} `{Link F}
    `{run_FnOnce_for_F : !FnOnce.Run F ('& T * '& T) Ordering.t}
    (v1 v2 : T) (compare : F) :
  Run.Trait cmp.max_by [] [ Φ T; Φ F ] [ φ v1; φ v2; φ compare ] T.
Proof.
  constructor.
  destruct run_FnOnce_for_F.
  run_symbolic.
Defined.
Global Opaque run_max_by.

(*
    pub trait Ord: Eq + PartialOrd<Self> {
        // Required method
        fn cmp(&self, other: &Self) -> Ordering;

        // Provided methods
        fn max(self, other: Self) -> Self
          where Self: Sized { ... }
        fn min(self, other: Self) -> Self
          where Self: Sized { ... }
        fn clamp(self, min: Self, max: Self) -> Self
          where Self: Sized + PartialOrd { ... }
    }
*)
Module Ord.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::cmp::Ord";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_cmp (Self : Set) `{Link Self} : Set := {
    cmp : PolymorphicFunction.t;
    cmp_is_method :: IsTraitMethod.C (trait Self) "cmp" cmp;
    run_cmp (self other : '& Self) :: Run.Trait cmp [] [] [ φ self; φ other ] Ordering.t;
  }.

  Class Method_max (Self : Set) `{Link Self} : Set := {
    max : PolymorphicFunction.t;
    max_is_method :: IsTraitMethod.C (trait Self) "max" max;
    run_max (self other : Self) :: Run.Trait max [] [] [ φ self; φ other ] Self;
  }.

  Class Method_min (Self : Set) `{Link Self} : Set := {
    min : PolymorphicFunction.t;
    min_is_method :: IsTraitMethod.C (trait Self) "min" min;
    run_min (self other : Self) :: Run.Trait min [] [] [ φ self; φ other ] Self;
  }.

  Class Method_clamp (Self : Set) `{Link Self} : Set := {
    clamp : PolymorphicFunction.t;
    clamp_is_method :: IsTraitMethod.C (trait Self) "clamp" clamp;
    run_clamp (self min max : Self) :: Run.Trait clamp [] [] [ φ self; φ min; φ max ] Self;
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    method_cmp :: Method_cmp Self;
    method_max :: Method_max Self;
    method_min :: Method_min Self;
    method_clamp :: Method_clamp Self;
  }.

  Module Provided.
    Instance run_min {Self : Set} `{Link Self} (self other : Self)
        `{!Method_cmp Self} :
      Run.Trait (cmp.cmp.Ord.min (Φ Self)) [] [] [ φ self; φ other ] Self.
    Proof.
      constructor.
      run_symbolic.
      exact (run_min_by value value0 (Function2.of_run _)).
    Defined.
    Global Opaque run_min.

    Instance run_max {Self : Set} `{Link Self} (self other : Self)
        {H_Method_cmp : Method_cmp Self} :
      Run.Trait (cmp.cmp.Ord.max (Φ Self)) [] [] [ φ self; φ other ] Self.
    Proof.
      constructor.
      run_symbolic.
      exact (run_max_by value value0 (Function2.of_run _)).
    Defined.
    Global Opaque run_max.

    Instance run_clamp {Self : Set} `{Link Self} (self min max : Self)
        `{!Method_cmp Self} :
      Run.Trait (cmp.cmp.Ord.clamp (Φ Self)) [] [] [ φ self; φ min; φ max ] Self.
    Proof.
    Admitted.
    Global Opaque run_clamp.
  End Provided.
  Export (hints) Provided.
End Ord.
Export (hints) Ord.

Instance run_min {T : Set} `{Link T} `{Ord.Run T} (v1 v2 : T) :
  Run.Trait cmp.min [] [ Φ T ] [ φ v1; φ v2 ] T.
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_min.

(* pub fn max<T: Ord>(v1: T, v2: T) -> T *)
Instance run_max {T : Set} `{Link T} `{Ord.Run T} (v1 v2 : T) :
  Run.Trait cmp.max [] [ Φ T ] [ φ v1; φ v2 ] T.
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_max.

Module Impl_Ord_for_u64.
  Definition Self : Set := u64.

  Instance method_cmp : Ord.Method_cmp Self.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply cmp.impls.Impl_core_cmp_Ord_for_u64.Implements. }
      { reflexivity. }
    }
    { constructor.
      run_symbolic.
    }
  Defined.

  Instance method_max : Ord.Method_max Self.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Provided.
      { apply cmp.impls.Impl_core_cmp_Ord_for_u64.Implements. }
      { reflexivity. }
      { apply cmp.Ord.ProvidedMethod_max. }
    }
    { typeclasses eauto. }
  Defined.

  Instance method_min : Ord.Method_min Self.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Provided.
      { apply cmp.impls.Impl_core_cmp_Ord_for_u64.Implements. }
      { reflexivity. }
      { apply cmp.Ord.ProvidedMethod_min. }
    }
    { typeclasses eauto. }
  Defined.

  Instance method_clamp : Ord.Method_clamp Self.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Provided.
      { apply cmp.impls.Impl_core_cmp_Ord_for_u64.Implements. }
      { reflexivity. }
      { apply cmp.Ord.ProvidedMethod_clamp. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run : Ord.Run Self := {}.
End Impl_Ord_for_u64.
Export (hints) Impl_Ord_for_u64.

Module Impl_Ord_for_usize.
  Definition Self : Set := usize.

  Instance method_cmp : Ord.Method_cmp Self.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply cmp.impls.Impl_core_cmp_Ord_for_usize.Implements. }
      { reflexivity. }
    }
    { constructor.
      run_symbolic.
    }
  Defined.

  Instance method_max : Ord.Method_max Self.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Provided.
      { apply cmp.impls.Impl_core_cmp_Ord_for_usize.Implements. }
      { reflexivity. }
      { apply cmp.Ord.ProvidedMethod_max. }
    }
    { typeclasses eauto. }
  Defined.

  Instance method_min : Ord.Method_min Self.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Provided.
      { apply cmp.impls.Impl_core_cmp_Ord_for_usize.Implements. }
      { reflexivity. }
      { apply cmp.Ord.ProvidedMethod_min. }
    }
    { typeclasses eauto. }
  Defined.

  Instance method_clamp : Ord.Method_clamp Self.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Provided.
      { apply cmp.impls.Impl_core_cmp_Ord_for_usize.Implements. }
      { reflexivity. }
      { apply cmp.Ord.ProvidedMethod_clamp. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run : Ord.Run Self := {}.
End Impl_Ord_for_usize.
Export (hints) Impl_Ord_for_usize.

(*
  pub trait PartialOrd<Rhs: ?Sized = Self>: PartialEq<Rhs> {
    fn partial_cmp(&self, other: &Rhs) -> Option<Ordering>;
    fn lt(&self, other: &Rhs) -> bool;
    fn le(&self, other: &Rhs) -> bool;
    fn gt(&self, other: &Rhs) -> bool;
    fn ge(&self, other: &Rhs) -> bool;
  }
*)
Module PartialOrd.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::cmp::PartialOrd";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [ Φ Rhs ];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_partial_cmp (Self Rhs : Set) `{Link Self} `{Link Rhs} : Set := {
    partial_cmp : PolymorphicFunction.t;
    partial_cmp_is_method :: IsTraitMethod.C (trait Self Rhs) "partial_cmp" partial_cmp;
    run_partial_cmp (self : '& Self) (other : '& Rhs) ::
      Run.Trait partial_cmp [] [] [ φ self; φ other ] (option Ordering.t);
  }.

  Class Method_lt (Self Rhs : Set) `{Link Self} `{Link Rhs} : Set := {
    lt : PolymorphicFunction.t;
    lt_is_method :: IsTraitMethod.C (trait Self Rhs) "lt" lt;
    run_lt (self : '& Self) (other : '& Rhs) :: Run.Trait lt [] [] [ φ self; φ other ] bool;
  }.

  Class Method_le (Self Rhs : Set) `{Link Self} `{Link Rhs} : Set := {
    le : PolymorphicFunction.t;
    le_is_method :: IsTraitMethod.C (trait Self Rhs) "le" le;
    run_le (self : '& Self) (other : '& Rhs) :: Run.Trait le [] [] [ φ self; φ other ] bool;
  }.

  Class Method_gt (Self Rhs : Set) `{Link Self} `{Link Rhs} : Set := {
    gt : PolymorphicFunction.t;
    gt_is_method :: IsTraitMethod.C (trait Self Rhs) "gt" gt;
    run_gt (self : '& Self) (other : '& Rhs) :: Run.Trait gt [] [] [ φ self; φ other ] bool;
  }.

  Class Method_ge (Self Rhs : Set) `{Link Self} `{Link Rhs} : Set := {
    ge : PolymorphicFunction.t;
    ge_is_method :: IsTraitMethod.C (trait Self Rhs) "ge" ge;
    run_ge (self : '& Self) (other : '& Rhs) :: Run.Trait ge [] [] [ φ self; φ other ] bool;
  }.

  Class Run (Self Rhs : Set) `{Link Self} `{Link Rhs} : Set := {
    method_partial_cmp :: Method_partial_cmp Self Rhs;
    method_lt :: Method_lt Self Rhs;
    method_le :: Method_le Self Rhs;
    method_gt :: Method_gt Self Rhs;
    method_ge :: Method_ge Self Rhs;
  }.
End PartialOrd.
Export (hints) PartialOrd.

Module Impl_PartialEq_for_Ordering.
  Definition Self : Set := Ordering.t.

  Instance run : PartialEq.Run Self Self.
  Admitted.
End Impl_PartialEq_for_Ordering.
Export (hints) Impl_PartialEq_for_Ordering.

Module Impl_PartialEq_for_U8.
  Definition Self : Set := u8.

  Instance run : PartialEq.Run Self Self.
  Admitted.
End Impl_PartialEq_for_U8.
Export (hints) Impl_PartialEq_for_U8.

Module Impl_PartialEq_for_Array.
  Definition Self (T U : Set) (N : usize) `{Link T} `{Link U} : Set :=
    array.t T N.

  Instance run
    (T U : Set) (N : usize) `{Link T} `{Link U} `{PartialEq.Run T U}
    : PartialEq.Run (array.t T N) (array.t U N).
  Admitted.
End Impl_PartialEq_for_Array.
Export (hints) Impl_PartialEq_for_Array.

Module Impl_PartialEq_for_Ref.
  Definition Self (A B : Set) `{Link A} `{Link B} : Set :=  
  '& A.

  Instance run
    (A B : Set) `{Link A} `{Link B} 
    : PartialEq.Run ('& A) ('& B).
  Admitted.
End Impl_PartialEq_for_Ref.
Export (hints) Impl_PartialEq_for_Ref.

Module Impl_PartialOrd_for_U32.
  Definition Self : Set := u32.

  Instance run : PartialOrd.Run Self Self.
  Admitted.
End Impl_PartialOrd_for_U32.
Export (hints) Impl_PartialOrd_for_U32.

Module Impl_PartialOrd_for_Ref.
  Definition Self (A : Set) `{Link A} : Set :=
    '& A.

  Instance run (A B : Set) `{Link A} `{Link B}
    {run_PartialOrd_for_A : PartialOrd.Run A B} :
    PartialOrd.Run ('& A) ('& B).
  Admitted.
End Impl_PartialOrd_for_Ref.
Export (hints) Impl_PartialOrd_for_Ref.
