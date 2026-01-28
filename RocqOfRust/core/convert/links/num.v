Require Import links.RocqOfRust.
Require Import core.convert.links.mod.
Require Import core.convert.num.
Require Import core.links.result.
Require Import core.num.links.error.

Module Impl_TryFrom_u64_for_usize.
  Definition Self : Set :=
    usize.

  Instance run_try_from (value : u64) :
    Run.Trait convert.num.ptr_try_from_impls.Impl_core_convert_TryFrom_u64_for_usize.try_from
      [] [] [φ value]
      (Result.t Self TryFromIntError.t).
  Proof.
    constructor.
    run_symbolic.
    { eapply Result.Ok; shelve. }
    { with_strategy transparent [φ] reflexivity. }
  Defined.

  Instance method_try_from : TryFrom.Method_try_from Self u64 TryFromIntError.t.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply convert.num.ptr_try_from_impls.Impl_core_convert_TryFrom_u64_for_usize.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run : TryFrom.Run Self u64 TryFromIntError.t := {}.
End Impl_TryFrom_u64_for_usize.
Export (hints) Impl_TryFrom_u64_for_usize.

Module Impl_TryFrom_u64_for_isize.
  Definition Self : Set :=
    isize.

  Instance run_try_from (value : u64) :
    Run.Trait convert.num.ptr_try_from_impls.Impl_core_convert_TryFrom_u64_for_isize.try_from
      [] [] [φ value]
      (Result.t Self TryFromIntError.t).
  Proof.
    constructor.
    run_symbolic.
    all: admit.
  Admitted.

  Instance method_try_from : TryFrom.Method_try_from Self u64 TryFromIntError.t.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply convert.num.ptr_try_from_impls.Impl_core_convert_TryFrom_u64_for_isize.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run : TryFrom.Run Self u64 TryFromIntError.t := {}.
End Impl_TryFrom_u64_for_isize.
Export (hints) Impl_TryFrom_u64_for_isize.
