Require Import simulate.RocqOfRust.
From Stdlib Require Import List.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import revm.revm_state.simulate.account_info.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.

Import ListNotations.

(** The flags and account methods follow revm_state/lib.rs. Maps are represented
    by association lists; their keys and values retain the Rust types. *)
Module AccountStatus.
  Definition t := u8.

  Definition Created : t := 1.

  Definition CreatedLocal : t := 128.

  Definition SelfDestructed : t := 2.

  Definition SelfDestructedLocal : t := 64.

  Definition Touched : t := 4.

  Definition LoadedAsNotExisting : t := 8.

  Definition Cold : t := 16.

  Definition empty : t := 0.

  Definition contains (self flag : t) : bool :=
    Z.eqb (Z.land self.(Integer.value) flag.(Integer.value)) flag.(Integer.value).

  Definition insert (self flag : t) : t :=
    {| Integer.value := Z.lor self.(Integer.value) flag.(Integer.value) |}.

  Definition remove (self flag : t) : t :=
    {| Integer.value := Z.land self.(Integer.value) (Z.lnot flag.(Integer.value)) |}.
End AccountStatus.

Module EvmStorageSlot.
  Record t : Set := {
    original_value : aliases.U256.t;
    present_value : aliases.U256.t;
    transaction_id : usize;
    is_cold : bool;
  }.
End EvmStorageSlot.

Module Account.
  Record t : Set := {
    info : AccountInfo.t;
    transaction_id : usize;
    storage : list (aliases.U256.t * EvmStorageSlot.t);
    status : AccountStatus.t;
  }.
End Account.

Module Impl_Default_for_Account.
  Definition default : Account.t := {|
    Account.info := Impl_Default_for_AccountInfo.default;
    Account.transaction_id := 0;
    Account.storage := [];
    Account.status := AccountStatus.empty;
  |}.
End Impl_Default_for_Account.

Module Impl_Account.
  Definition new_not_existing (transaction_id : usize) : Account.t := {|
    Account.info := Impl_Default_for_AccountInfo.default;
    Account.transaction_id := transaction_id;
    Account.storage := [];
    Account.status := AccountStatus.LoadedAsNotExisting;
  |}.

  Definition mark_selfdestruct (self : Account.t) : Account.t :=
    self <| Account.status := AccountStatus.insert self.(Account.status) AccountStatus.SelfDestructed |>.

  Definition unmark_selfdestruct (self : Account.t) : Account.t :=
    self <| Account.status := AccountStatus.remove self.(Account.status) AccountStatus.SelfDestructed |>.

  Definition is_selfdestructed (self : Account.t) : bool :=
    AccountStatus.contains self.(Account.status) AccountStatus.SelfDestructed.

  Definition mark_touch (self : Account.t) : Account.t :=
    self <| Account.status := AccountStatus.insert self.(Account.status) AccountStatus.Touched |>.

  Definition unmark_touch (self : Account.t) : Account.t :=
    self <| Account.status := AccountStatus.remove self.(Account.status) AccountStatus.Touched |>.

  Definition is_touched (self : Account.t) : bool :=
    AccountStatus.contains self.(Account.status) AccountStatus.Touched.

  Definition mark_created (self : Account.t) : Account.t :=
    self <| Account.status := AccountStatus.insert self.(Account.status) AccountStatus.Created |>.

  Definition unmark_created (self : Account.t) : Account.t :=
    self <| Account.status := AccountStatus.remove self.(Account.status) AccountStatus.Created |>.

  Definition mark_cold (self : Account.t) : Account.t :=
    self <| Account.status := AccountStatus.insert self.(Account.status) AccountStatus.Cold |>.

  Definition is_cold_transaction_id (self : Account.t) (transaction_id : usize) : bool :=
    (self.(Account.transaction_id) !=i transaction_id) ||
      AccountStatus.contains self.(Account.status) AccountStatus.Cold.

  Definition mark_warm_with_transaction_id (self : Account.t) (transaction_id : usize)
      : bool * Account.t :=
    let is_cold := is_cold_transaction_id self transaction_id in
    (is_cold, self
      <| Account.status := AccountStatus.remove self.(Account.status) AccountStatus.Cold |>
      <| Account.transaction_id := transaction_id |>).

  Definition is_created_locally (self : Account.t) : bool :=
    AccountStatus.contains self.(Account.status) AccountStatus.CreatedLocal.

  Definition is_selfdestructed_locally (self : Account.t) : bool :=
    AccountStatus.contains self.(Account.status) AccountStatus.SelfDestructedLocal.

  Definition selfdestruct (self : Account.t) : Account.t :=
    self <| Account.storage := [] |> <| Account.info := Impl_Default_for_AccountInfo.default |>.

  Definition mark_created_locally (self : Account.t) : bool * Account.t :=
    let self := self
      <| Account.status := AccountStatus.insert self.(Account.status) AccountStatus.CreatedLocal |> in
    let is_created_globally := negb (AccountStatus.contains self.(Account.status) AccountStatus.Created) in
    (is_created_globally, mark_created self).

  Definition unmark_created_locally (self : Account.t) : Account.t :=
    self <| Account.status := AccountStatus.remove self.(Account.status) AccountStatus.CreatedLocal |>.

  Definition mark_selfdestructed_locally (self : Account.t) : bool * Account.t :=
    let self := self
      <| Account.status := AccountStatus.insert self.(Account.status) AccountStatus.SelfDestructedLocal |> in
    let is_global_selfdestructed := negb (is_selfdestructed self) in
    (is_global_selfdestructed, mark_selfdestruct self).

  Definition unmark_selfdestructed_locally (self : Account.t) : Account.t :=
    self <| Account.status := AccountStatus.remove self.(Account.status) AccountStatus.SelfDestructedLocal |>.

  Definition is_loaded_as_not_existing (self : Account.t) : bool :=
    AccountStatus.contains self.(Account.status) AccountStatus.LoadedAsNotExisting.

  Definition is_loaded_as_not_existing_not_touched (self : Account.t) : bool :=
    is_loaded_as_not_existing self && negb (is_touched self).

  Definition is_created (self : Account.t) : bool :=
    AccountStatus.contains self.(Account.status) AccountStatus.Created.

  Definition is_empty (self : Account.t) : bool :=
    Impl_AccountInfo.is_empty self.(Account.info).

  Definition state_clear_aware_is_empty (self : Account.t) (spec : SpecId.t) : bool :=
    if Impl_SpecId.is_enabled_in spec SpecId.SPURIOUS_DRAGON
    then is_empty self else is_loaded_as_not_existing_not_touched self.

  Definition caller_initial_modification (self : Account.t) (new_balance : aliases.U256.t)
      (is_call : bool) : aliases.U256.t * Account.t :=
    let self := mark_touch self in
    let info := self.(Account.info) in
    let info := if is_call then
      info <| AccountInfo.nonce := BinOp.Saturating.add info.(AccountInfo.nonce) 1 |>
      else info in
    (info.(AccountInfo.balance), self
      <| Account.info := info <| AccountInfo.balance := new_balance |> |>).
End Impl_Account.

Module Impl_EvmStorageSlot.
  Definition new (original : aliases.U256.t) (transaction_id : usize) : EvmStorageSlot.t := {|
    EvmStorageSlot.original_value := original;
    EvmStorageSlot.present_value := original;
    EvmStorageSlot.transaction_id := transaction_id;
    EvmStorageSlot.is_cold := false;
  |}.

  Definition new_changed (original_value present_value : aliases.U256.t)
      (transaction_id : usize) : EvmStorageSlot.t := {|
    EvmStorageSlot.original_value := original_value;
    EvmStorageSlot.present_value := present_value;
    EvmStorageSlot.transaction_id := transaction_id;
    EvmStorageSlot.is_cold := false;
  |}.

  Definition is_changed (self : EvmStorageSlot.t) : bool :=
    negb (Z.eqb self.(EvmStorageSlot.original_value).(Uint.value)
      self.(EvmStorageSlot.present_value).(Uint.value)).

  Definition mark_cold (self : EvmStorageSlot.t) : EvmStorageSlot.t :=
    self <| EvmStorageSlot.is_cold := true |>.

  Definition is_cold_transaction_id (self : EvmStorageSlot.t) (transaction_id : usize) : bool :=
    (self.(EvmStorageSlot.transaction_id) !=i transaction_id) || self.(EvmStorageSlot.is_cold).

  Definition mark_warm_with_transaction_id (self : EvmStorageSlot.t) (transaction_id : usize)
      : bool * EvmStorageSlot.t :=
    let is_cold := is_cold_transaction_id self transaction_id in
    (is_cold, self <| EvmStorageSlot.transaction_id := transaction_id |>
      <| EvmStorageSlot.is_cold := false |>).
End Impl_EvmStorageSlot.
