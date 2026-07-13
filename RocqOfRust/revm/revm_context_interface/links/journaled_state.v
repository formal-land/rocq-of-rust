Require Import links.RocqOfRust.
Require Import alloc.borrow.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.bytes.links.mod.
Require Import core.links.option.
Require Import core.ops.links.function.
Require Import core.ops.links.deref.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_context_interface.journaled_state.
Require Import ruint.links.lib.

(*
pub struct StateLoad<T> {
    pub data: T,
    pub is_cold: bool,
}
*)
Module StateLoad.
  RocqOfRustLinkGenericRecord "revm_context_interface::journaled_state::StateLoad" [ T ] := {
    data : T;
    is_cold : bool
  }.
End StateLoad.
Export (hints) StateLoad.

(*
impl<T> Deref for StateLoad<T> {
    type Target = T;
*)
Module Impl_Deref_for_StateLoad.
  Definition Self (T : Set) `{Link T} : Set :=
    StateLoad.t T.

  Instance run_deref (T : Set) `{Link T} (self : '& (Self T)) :
    Run.Trait
      (journaled_state.Impl_core_ops_deref_Deref_for_revm_context_interface_journaled_state_StateLoad_T.deref (Φ T))
      [] [] [ φ self ] ('& T).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_deref.

  Instance method_deref (T : Set) `{Link T} : Deref.Method_deref (Self T) T.
  Proof.
    econstructor.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply journaled_state.Impl_core_ops_deref_Deref_for_revm_context_interface_journaled_state_StateLoad_T.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run (T : Set) `{Link T} : Deref.Run (Self T) T :=
  {}.
End Impl_Deref_for_StateLoad.
Export (hints) Impl_Deref_for_StateLoad.

Module Impl_StateLoad.
  Definition Self (T : Set) `{Link T} : Set :=
    StateLoad.t T.

  Instance run_new (T : Set) `{Link T} (data : T) (is_cold : bool) :
    Run.Trait
      (journaled_state.Impl_revm_context_interface_journaled_state_StateLoad_T.new (Φ T))
      [] [] [ φ data; φ is_cold ] (Self T).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_new.
End Impl_StateLoad.
Export (hints) Impl_StateLoad.

(*
pub struct Eip7702CodeLoad<T> {
    pub state_load: StateLoad<T>,
    pub is_delegate_account_cold: Option<bool>,
}
*)
Module Eip7702CodeLoad.
  RocqOfRustLinkGenericRecord "revm_context_interface::journaled_state::Eip7702CodeLoad" [ T ] := {
    state_load : (StateLoad.t T);
    is_delegate_account_cold : (option bool)
  }.
End Eip7702CodeLoad.
Export (hints) Eip7702CodeLoad.

(*
pub struct AccountLoad {
    pub is_delegate_account_cold: Option<bool>,
    pub is_empty: bool,
}
*)
Module AccountLoad.
  RocqOfRustLinkRecord "revm_context_interface::journaled_state::AccountLoad" := {
    is_delegate_account_cold : (option bool);
    is_empty : bool
  }.
End AccountLoad.
Export (hints) AccountLoad.

Module Cow.
  RocqOfRustLinkGenericEnum "alloc::borrow::Cow" [ T ] :=
  | Borrowed (value : ('& T))
  | Owned (value : T)
  .
End Cow.
Export (hints) Cow.

Module AccountInfo.
  RocqOfRustLinkRecord "revm_state::account_info::AccountInfo" := {
    balance : aliases.U256.t;
    nonce : u64;
    code_hash : aliases.B256.t;
    code : (option Bytecode.t)
  }.
End AccountInfo.
Export (hints) AccountInfo.

Module Impl_Deref_for_Cow.
  Definition Self (T : Set) `{Link T} : Set :=
    Cow.t T.

  Instance run_deref (T : Set) `{Link T} (self : '& (Self T)) :
    Run.Trait
      (borrow.Impl_core_ops_deref_Deref_where_core_marker_Sized_B_where_alloc_borrow_ToOwned_B_for_alloc_borrow_Cow_B.deref (Φ T))
      [] [] [ φ self ] ('& T).
  Admitted.
  Global Opaque run_deref.

  Instance method_deref (T : Set) `{Link T} : Deref.Method_deref (Self T) T.
  Proof.
    econstructor.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply borrow.Impl_core_ops_deref_Deref_where_core_marker_Sized_B_where_alloc_borrow_ToOwned_B_for_alloc_borrow_Cow_B.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run (T : Set) `{Link T} : Deref.Run (Self T) T :=
  {}.
End Impl_Deref_for_Cow.
Export (hints) Impl_Deref_for_Cow.

(*
pub struct AccountInfoLoad<'a> {
    pub account: Cow<'a, AccountInfo>,
    pub is_cold: bool,
    pub is_empty: bool,
}
*)
Module AccountInfoLoad.
  RocqOfRustLinkRecord "revm_context_interface::journaled_state::AccountInfoLoad" := {
    account : (Cow.t AccountInfo.t);
    is_cold : bool;
    is_empty : bool
  }.
End AccountInfoLoad.
Export (hints) AccountInfoLoad.

Module Impl_AccountInfoLoad.
  Definition Self : Set :=
    AccountInfoLoad.t.

  Instance run_into_state_load {F O : Set} `{Link F} `{Link O}
      (Run_FnOnce_for_F : function.FnOnce.Run F (OneElementTuple.t (Cow.t AccountInfo.t)) O)
      (self : Self) (f : F) :
    Run.Trait
      journaled_state.Impl_revm_context_interface_journaled_state_AccountInfoLoad.into_state_load
      [] [ Φ F; Φ O ] [ φ self; φ f ]
      (StateLoad.t O).
  Proof.
    constructor.
    run_symbolic.
    eapply Run.CallPrimitiveGetTraitMethod.
    { exact Run_FnOnce_for_F.(function.FnOnce.method_call_once).(function.FnOnce.call_once_is_method).(IsTraitMethod.Make). }
    run_symbolic.
  Defined.
  Global Opaque run_into_state_load.
End Impl_AccountInfoLoad.
Export (hints) Impl_AccountInfoLoad.

Module Impl_Deref_for_AccountInfoLoad.
  Definition Self : Set :=
    AccountInfoLoad.t.

  Instance run_deref (self : '& Self) :
    Run.Trait
      journaled_state.Impl_core_ops_deref_Deref_for_revm_context_interface_journaled_state_AccountInfoLoad.deref
      [] [] [ φ self ] ('& AccountInfo.t).
  Proof.
    constructor.
    run_symbolic.
    eapply Run.CallPrimitiveGetTraitMethod.
    { exact (Impl_Deref_for_Cow.method_deref AccountInfo.t).(deref.Deref.deref_is_method).(IsTraitMethod.Make). }
    run_symbolic.
  Defined.
  Global Opaque run_deref.

  Instance method_deref : Deref.Method_deref Self AccountInfo.t.
  Proof.
    econstructor.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply journaled_state.Impl_core_ops_deref_Deref_for_revm_context_interface_journaled_state_AccountInfoLoad.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run : Deref.Run Self AccountInfo.t :=
  {}.
End Impl_Deref_for_AccountInfoLoad.
Export (hints) Impl_Deref_for_AccountInfoLoad.
