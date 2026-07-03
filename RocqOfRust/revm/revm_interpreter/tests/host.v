Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.common.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.log.links.mod.
Require Import core.links.result.
Require Import revm.revm_context_interface.links.cfg.
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

  Definition block_number (self : t) :
      aliases.U256.t * t :=
    (Impl_Uint.ZERO, Make).

  Definition host_chain_id (self : t) :
      aliases.U256.t * t :=
    ({| Uint.value := 1 |}, Make).

  Definition host_basefee (self : t) :
      aliases.U256.t * t :=
    (Impl_Uint.ZERO, Make).

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
      (_target : Address.t)
      (_skip_cold_load : bool) :
      Result.t (StateLoad.t SelfDestructResult.t) LoadError.t * t :=
    (Result.Err LoadError.DBError, Make).

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

  Definition effective_gas_price (_self : t) (_base_fee : u128) : u128 :=
    {| Integer.value := 42 |}.

  Instance Transaction_for_t : Transaction.C t transaction_types := {
    Transaction.tx_type _ := Make;
    Transaction.legacy := {|
      RefStub.path := [];
      RefStub.projection _ := Make;
      RefStub.injection _ _ := Make;
    |};
    Transaction.eip2930 := {|
      RefStub.path := [];
      RefStub.projection _ := Make;
      RefStub.injection _ _ := Make;
    |};
    Transaction.eip1559 := {|
      RefStub.path := [];
      RefStub.projection _ := Make;
      RefStub.injection _ _ := Make;
    |};
    Transaction.eip4844 := {|
      RefStub.path := [];
      RefStub.projection _ := Make;
      RefStub.injection _ _ := Make;
    |};
    Transaction.eip7702 := {|
      RefStub.path := [];
      RefStub.projection _ := Make;
      RefStub.injection _ _ := Make;
    |};
    Transaction.max_fee _ := {| Integer.value := 0 |};
    Transaction.effective_gas_price := effective_gas_price;
    Transaction.kind _ := TxKind.Create;
    Transaction.access_list _ := None;
  }.

  Instance TransactionGetter_for_t :
      TransactionGetter.C t
        host_types.(Host.Types.Transaction)
        host_types.(Host.Types.TransactionTypes) := {
    TransactionGetter.Transaction_for_Transaction := Transaction_for_t;
    TransactionGetter.tx := {|
      RefStub.path := [];
      RefStub.projection self := self;
      RefStub.injection _ y := y;
    |};
  }.

  Instance Block_for_t : Block.C t := {
    Block.number := number;
    Block.beneficiary := beneficiary;
    Block.timestamp := timestamp;
    Block.gas_limit := gas_limit;
    Block.basefee := basefee;
    Block.difficulty := difficulty;
    Block.prevrandao := prevrandao;
    Block.blob_excess_gas_and_price _ := None;
    Block.blob_gasprice := blob_gasprice;
    Block.blob_excess_gas _ := None;
  }.

  Instance BlockGetter_for_t :
      BlockGetter.C t (Host.Types.to_BlockGetter_types host_types) := {
    BlockGetter.Block_for_Block := Block_for_t;
    BlockGetter.block := block;
  }.

  Instance Cfg_for_t :
      Cfg.C t (CfgGetter.Types.to_Cfg_types (Host.Types.to_CfgGetter_types host_types)) := {
    Cfg.chain_id := chain_id;
    Cfg.spec := spec;
    Cfg.max_code_size := max_code_size;
    Cfg.is_eip3607_disabled := is_eip3607_disabled;
    Cfg.is_balance_check_disabled := is_balance_check_disabled;
    Cfg.is_gas_refund_disabled := is_gas_refund_disabled;
    Cfg.is_block_gas_limit_disabled := is_block_gas_limit_disabled;
    Cfg.is_nonce_check_disabled := is_nonce_check_disabled;
    Cfg.is_base_fee_check_disabled := is_base_fee_check_disabled;
  }.

  Instance CfgGetter_for_t :
      CfgGetter.C t (Host.Types.to_CfgGetter_types host_types) := {
    CfgGetter.Cfg_for_Cfg := Cfg_for_t;
    CfgGetter.cfg := cfg;
  }.

  Instance I : Host.C t host_types := {
    Host.TransactionGetter_for_Self := TransactionGetter_for_t;
    Host.BlockGetter_for_Self := BlockGetter_for_t;
    Host.CfgGetter_for_Self := CfgGetter_for_t;
    Host.load_account_delegated := load_account_delegated;
    Host.block_hash := block_hash;
    Host.block_number := block_number;
    Host.chain_id := host_chain_id;
    Host.basefee := host_basefee;
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

  Definition block_number (self : t) :
      aliases.U256.t * t :=
    (Impl_Uint.ZERO, Make).

  Definition host_chain_id (self : t) :
      aliases.U256.t * t :=
    ({| Uint.value := 1 |}, Make).

  Definition host_basefee (self : t) :
      aliases.U256.t * t :=
    (Impl_Uint.ZERO, Make).

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
      (_target : Address.t)
      (_skip_cold_load : bool) :
      Result.t (StateLoad.t SelfDestructResult.t) LoadError.t * t :=
    (Result.Err LoadError.DBError, Make).

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

  Definition effective_gas_price (_self : t) (_base_fee : u128) : u128 :=
    {| Integer.value := 42 |}.

  Instance Transaction_for_t : Transaction.C t transaction_types := {
    Transaction.tx_type _ := Make;
    Transaction.legacy := {|
      RefStub.path := [];
      RefStub.projection _ := Make;
      RefStub.injection _ _ := Make;
    |};
    Transaction.eip2930 := {|
      RefStub.path := [];
      RefStub.projection _ := Make;
      RefStub.injection _ _ := Make;
    |};
    Transaction.eip1559 := {|
      RefStub.path := [];
      RefStub.projection _ := Make;
      RefStub.injection _ _ := Make;
    |};
    Transaction.eip4844 := {|
      RefStub.path := [];
      RefStub.projection _ := Make;
      RefStub.injection _ _ := Make;
    |};
    Transaction.eip7702 := {|
      RefStub.path := [];
      RefStub.projection _ := Make;
      RefStub.injection _ _ := Make;
    |};
    Transaction.max_fee _ := {| Integer.value := 0 |};
    Transaction.effective_gas_price := effective_gas_price;
    Transaction.kind _ := TxKind.Create;
    Transaction.access_list _ := None;
  }.

  Instance TransactionGetter_for_t :
      TransactionGetter.C t
        host_types.(Host.Types.Transaction)
        host_types.(Host.Types.TransactionTypes) := {
    TransactionGetter.Transaction_for_Transaction := Transaction_for_t;
    TransactionGetter.tx := {|
      RefStub.path := [];
      RefStub.projection self := self;
      RefStub.injection _ y := y;
    |};
  }.

  Instance Block_for_t : Block.C t := {
    Block.number := number;
    Block.beneficiary := beneficiary;
    Block.timestamp := timestamp;
    Block.gas_limit := gas_limit;
    Block.basefee := basefee;
    Block.difficulty := difficulty;
    Block.prevrandao := prevrandao;
    Block.blob_excess_gas_and_price _ := None;
    Block.blob_gasprice := blob_gasprice;
    Block.blob_excess_gas _ := None;
  }.

  Instance BlockGetter_for_t :
      BlockGetter.C t (Host.Types.to_BlockGetter_types host_types) := {
    BlockGetter.Block_for_Block := Block_for_t;
    BlockGetter.block := block;
  }.

  Instance Cfg_for_t :
      Cfg.C t (CfgGetter.Types.to_Cfg_types (Host.Types.to_CfgGetter_types host_types)) := {
    Cfg.chain_id := chain_id;
    Cfg.spec := spec;
    Cfg.max_code_size := max_code_size;
    Cfg.is_eip3607_disabled := is_eip3607_disabled;
    Cfg.is_balance_check_disabled := is_balance_check_disabled;
    Cfg.is_gas_refund_disabled := is_gas_refund_disabled;
    Cfg.is_block_gas_limit_disabled := is_block_gas_limit_disabled;
    Cfg.is_nonce_check_disabled := is_nonce_check_disabled;
    Cfg.is_base_fee_check_disabled := is_base_fee_check_disabled;
  }.

  Instance CfgGetter_for_t :
      CfgGetter.C t (Host.Types.to_CfgGetter_types host_types) := {
    CfgGetter.Cfg_for_Cfg := Cfg_for_t;
    CfgGetter.cfg := cfg;
  }.

  Instance I : Host.C t host_types := {
    Host.TransactionGetter_for_Self := TransactionGetter_for_t;
    Host.BlockGetter_for_Self := BlockGetter_for_t;
    Host.CfgGetter_for_Self := CfgGetter_for_t;
    Host.load_account_delegated := load_account_delegated;
    Host.block_hash := block_hash;
    Host.block_number := block_number;
    Host.chain_id := host_chain_id;
    Host.basefee := host_basefee;
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
