Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.log.links.mod.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.links.transaction.
Require Import revm.revm_context_interface.simulate.block.
Require Import revm.revm_context_interface.simulate.cfg.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_context_interface.simulate.transaction.
Require Import ruint.links.lib.
Require Import ruint.simulate.lib.

(** Mock Host that returns None - for FatalExternalError path *)
Module TestHost.
  Inductive t : Set := Make.

  Instance IsLink : Link t.
  Admitted.

  Definition cfg : RefStub.t t t := {|
    RefStub.path := [];
    RefStub.projection self := self;
    RefStub.injection _ y := y;
  |}.
  Definition block : RefStub.t t t := {|
    RefStub.path := [];
    RefStub.projection self := self;
    RefStub.injection _ y := y;
  |}.

  Definition chain_id (_self : t) : u64 := {| Integer.value := 1 |}.
  Definition spec (_self : t) : t := Make.
  Definition max_code_size (_self : t) : usize := {| Integer.value := 0 |}.
  Definition is_eip3607_disabled (_self : t) : bool := false.
  Definition is_balance_check_disabled (_self : t) : bool := false.
  Definition is_gas_refund_disabled (_self : t) : bool := false.
  Definition is_block_gas_limit_disabled (_self : t) : bool := false.
  Definition is_nonce_check_disabled (_self : t) : bool := false.
  Definition is_base_fee_check_disabled (_self : t) : bool := false.
  Definition number (_self : t) : u64 := {| Integer.value := 1 |}.
  Definition beneficiary (_self : t) : Address.t := {| Address.value := 0 |}.
  Definition timestamp (_self : t) : u64 := {| Integer.value := 0 |}.
  Definition gas_limit (_self : t) : u64 := {| Integer.value := 0 |}.
  Definition basefee (_self : t) : u64 := {| Integer.value := 0 |}.
  Definition difficulty (_self : t) : aliases.U256.t := Impl_Uint.ZERO.
  Definition prevrandao (_self : t) : option aliases.B256.t := None.
  Definition blob_gasprice (_self : t) : option u128 := None.

  Definition load_account_delegated (self : t) (_address : Address.t) :
      option AccountLoad.t * t :=
    (None, Make).

  Definition block_hash (self : t) (_number : u64) :
      option aliases.B256.t * t :=
    (None, Make).

  Definition balance (self : t) (_address : Address.t) :
      option (StateLoad.t aliases.U256.t) * t :=
    (None, Make).

  Definition code (self : t) (_address : Address.t) :
      option (Eip7702CodeLoad.t Bytes.t) * t :=
    (None, Make).

  Definition code_hash (self : t) (_address : Address.t) :
      option (Eip7702CodeLoad.t aliases.B256.t) * t :=
    (None, Make).

  Definition sload (self : t) (_address : Address.t) (_index : aliases.U256.t) :
      option (StateLoad.t aliases.U256.t) * t :=
    (None, Make).

  Definition sstore
      (self : t)
      (_address : Address.t)
      (_index : aliases.U256.t)
      (_value : aliases.U256.t) :
      option (StateLoad.t SStoreResult.t) * t :=
    (None, Make).

  Definition tload (self : t) (_address : Address.t) (_index : aliases.U256.t) :
      aliases.U256.t * t :=
    (Impl_Uint.ZERO, Make).

  Definition tstore
      (self : t)
      (_address : Address.t)
      (_index : aliases.U256.t)
      (_value : aliases.U256.t) :
      t :=
    Make.

  Definition log (self : t) (_log : Log.t LogData.t) : t :=
    Make.

  Definition selfdestruct
      (self : t)
      (_address : Address.t)
      (_target : Address.t) :
      option (StateLoad.t SelfDestructResult.t) * t :=
    (None, Make).

  Definition transaction_types : Transaction.Types.t := {|
    Transaction.Types.TransactionError := t;
    Transaction.Types.TransactionType := t;
    Transaction.Types.AccessList := t;
    Transaction.Types.Legacy := t;
    Transaction.Types.Eip2930 := t;
    Transaction.Types.Eip1559 := t;
    Transaction.Types.Eip4844 := t;
    Transaction.Types.Eip7702 := t;
  |}.

  Instance transaction_types_are_links :
    Transaction.Types.AreLinks transaction_types := {}.

  Definition host_types : Host.Types.t := {|
    Host.Types.Transaction := t;
    Host.Types.TransactionTypes := transaction_types;
    Host.Types.Cfg := t;
    Host.Types.Spec := t;
    Host.Types.Block := t;
  |}.

  Instance host_types_are_links : Host.Types.AreLinks host_types := {}.

  Instance TransactionGetter_for_t :
      TransactionGetter.C t
        host_types.(Host.Types.Transaction)
        host_types.(Host.Types.TransactionTypes).
  Admitted.

  Instance BlockGetter_for_t :
      BlockGetter.C t (Host.Types.to_BlockGetter_types host_types).
  Admitted.

  Instance CfgGetter_for_t :
      CfgGetter.C t (Host.Types.to_CfgGetter_types host_types).
  Admitted.

  Instance I : Host.C t host_types := {
    Host.TransactionGetter_for_Self := TransactionGetter_for_t;
    Host.BlockGetter_for_Self := BlockGetter_for_t;
    Host.CfgGetter_for_Self := CfgGetter_for_t;
    Host.load_account_delegated := load_account_delegated;
    Host.block_hash := block_hash;
    Host.balance := balance;
    Host.code := code;
    Host.code_hash := code_hash;
    Host.sload := sload;
    Host.sstore := sstore;
    Host.tload := tload;
    Host.tstore := tstore;
    Host.log := log;
    Host.selfdestruct := selfdestruct;
  }.
End TestHost.
Export (hints) TestHost.

(** Mock Host that returns Some - for success path *)
Module TestHostWithAccount.
  Inductive t : Set := Make.

  Instance IsLink : Link t.
  Admitted.

  Definition cfg : RefStub.t t t := {|
    RefStub.path := [];
    RefStub.projection self := self;
    RefStub.injection _ y := y;
  |}.
  Definition block : RefStub.t t t := {|
    RefStub.path := [];
    RefStub.projection self := self;
    RefStub.injection _ y := y;
  |}.

  Definition chain_id (_self : t) : u64 := {| Integer.value := 1 |}.
  Definition spec (_self : t) : t := Make.
  Definition max_code_size (_self : t) : usize := {| Integer.value := 0 |}.
  Definition is_eip3607_disabled (_self : t) : bool := false.
  Definition is_balance_check_disabled (_self : t) : bool := false.
  Definition is_gas_refund_disabled (_self : t) : bool := false.
  Definition is_block_gas_limit_disabled (_self : t) : bool := false.
  Definition is_nonce_check_disabled (_self : t) : bool := false.
  Definition is_base_fee_check_disabled (_self : t) : bool := false.
  Definition number (_self : t) : u64 := {| Integer.value := 1 |}.
  Definition beneficiary (_self : t) : Address.t := {| Address.value := 0 |}.
  Definition timestamp (_self : t) : u64 := {| Integer.value := 0 |}.
  Definition gas_limit (_self : t) : u64 := {| Integer.value := 0 |}.
  Definition basefee (_self : t) : u64 := {| Integer.value := 0 |}.
  Definition difficulty (_self : t) : aliases.U256.t := Impl_Uint.ZERO.
  Definition prevrandao (_self : t) : option aliases.B256.t := None.
  Definition blob_gasprice (_self : t) : option u128 := None.

  Definition test_account_load : AccountLoad.t := {|
    AccountLoad.load := {|
      Eip7702CodeLoad.state_load := {|
        StateLoad.data := tt;
        StateLoad.is_cold := false;
      |};
      Eip7702CodeLoad.is_delegate_account_cold := None;
    |};
    AccountLoad.is_empty := true;
  |}.

  Definition load_account_delegated (self : t) (_address : Address.t) :
      option AccountLoad.t * t :=
    (Some test_account_load, Make).

  Definition block_hash (self : t) (_number : u64) :
      option aliases.B256.t * t :=
    (None, Make).

  Definition balance (self : t) (_address : Address.t) :
      option (StateLoad.t aliases.U256.t) * t :=
    (None, Make).

  Definition code (self : t) (_address : Address.t) :
      option (Eip7702CodeLoad.t Bytes.t) * t :=
    (None, Make).

  Definition code_hash (self : t) (_address : Address.t) :
      option (Eip7702CodeLoad.t aliases.B256.t) * t :=
    (None, Make).

  Definition sload (self : t) (_address : Address.t) (_index : aliases.U256.t) :
      option (StateLoad.t aliases.U256.t) * t :=
    (None, Make).

  Definition sstore
      (self : t)
      (_address : Address.t)
      (_index : aliases.U256.t)
      (_value : aliases.U256.t) :
      option (StateLoad.t SStoreResult.t) * t :=
    (None, Make).

  Definition tload (self : t) (_address : Address.t) (_index : aliases.U256.t) :
      aliases.U256.t * t :=
    (Impl_Uint.ZERO, Make).

  Definition tstore
      (self : t)
      (_address : Address.t)
      (_index : aliases.U256.t)
      (_value : aliases.U256.t) :
      t :=
    Make.

  Definition log (self : t) (_log : Log.t LogData.t) : t :=
    Make.

  Definition selfdestruct
      (self : t)
      (_address : Address.t)
      (_target : Address.t) :
      option (StateLoad.t SelfDestructResult.t) * t :=
    (None, Make).

  Definition transaction_types : Transaction.Types.t := {|
    Transaction.Types.TransactionError := t;
    Transaction.Types.TransactionType := t;
    Transaction.Types.AccessList := t;
    Transaction.Types.Legacy := t;
    Transaction.Types.Eip2930 := t;
    Transaction.Types.Eip1559 := t;
    Transaction.Types.Eip4844 := t;
    Transaction.Types.Eip7702 := t;
  |}.

  Instance transaction_types_are_links :
    Transaction.Types.AreLinks transaction_types := {}.

  Definition host_types : Host.Types.t := {|
    Host.Types.Transaction := t;
    Host.Types.TransactionTypes := transaction_types;
    Host.Types.Cfg := t;
    Host.Types.Spec := t;
    Host.Types.Block := t;
  |}.

  Instance host_types_are_links : Host.Types.AreLinks host_types := {}.

  Instance TransactionGetter_for_t :
      TransactionGetter.C t
        host_types.(Host.Types.Transaction)
        host_types.(Host.Types.TransactionTypes).
  Admitted.

  Instance BlockGetter_for_t :
      BlockGetter.C t (Host.Types.to_BlockGetter_types host_types).
  Admitted.

  Instance CfgGetter_for_t :
      CfgGetter.C t (Host.Types.to_CfgGetter_types host_types).
  Admitted.

  Instance I : Host.C t host_types := {
    Host.TransactionGetter_for_Self := TransactionGetter_for_t;
    Host.BlockGetter_for_Self := BlockGetter_for_t;
    Host.CfgGetter_for_Self := CfgGetter_for_t;
    Host.load_account_delegated := load_account_delegated;
    Host.block_hash := block_hash;
    Host.balance := balance;
    Host.code := code;
    Host.code_hash := code_hash;
    Host.sload := sload;
    Host.sstore := sstore;
    Host.tload := tload;
    Host.tstore := tstore;
    Host.log := log;
    Host.selfdestruct := selfdestruct;
  }.
End TestHostWithAccount.
Export (hints) TestHostWithAccount.
