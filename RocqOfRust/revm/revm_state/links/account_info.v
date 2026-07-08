Require Import links.RocqOfRust.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_state.account_info.

Module Impl_AccountInfo.
  Instance run_is_empty (self : '& AccountInfo.t) :
    Run.Trait
      account_info.Impl_revm_state_account_info_AccountInfo.is_empty
      [] [] [ φ self ]
      bool.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_is_empty.
End Impl_AccountInfo.
Export (hints) Impl_AccountInfo.
