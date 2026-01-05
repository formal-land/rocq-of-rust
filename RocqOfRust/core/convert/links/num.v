Require Import RocqOfRust.RocqOfRust.
Require Import links.M.
Require Import core.convert.links.mod.
Require Import core.convert.num.
Require Import core.links.result.
Require Import core.num.links.error.

Module Impl_TryFrom_u64_for_usize.
  Definition Self : Set :=
    usize.

  Definition run_try_from : TryFrom.Run_try_from Self u64 TryFromIntError.t.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply convert.num.ptr_try_from_impls.Impl_core_convert_TryFrom_u64_for_usize.Implements. }
      { reflexivity. }
    }
    { constructor.
      run_symbolic.
      { eapply Result.Ok; shelve. }
      { with_strategy transparent [φ] reflexivity. }
    }
  Defined.

  Instance run : TryFrom.Run Self u64 TryFromIntError.t := {
    TryFrom.try_from := run_try_from;
  }.
End Impl_TryFrom_u64_for_usize.

Module Impl_TryFrom_u64_for_isize.
  Definition Self : Set :=
    isize.

  Definition run_try_from : TryFrom.Run_try_from Self u64 TryFromIntError.t.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply convert.num.ptr_try_from_impls.Impl_core_convert_TryFrom_u64_for_isize.Implements. }
      { reflexivity. }
    }
    { constructor.
      run_symbolic.
      all: admit.
    }
  Admitted.

  Instance run : TryFrom.Run Self u64 TryFromIntError.t := {
    TryFrom.try_from := run_try_from;
  }.
End Impl_TryFrom_u64_for_isize.
