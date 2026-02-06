Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.log.links.mod.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.instructions.simulate.contract.static_call.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
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

  Definition load_account_delegated (self : t) (address : Address.t) :
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

  Instance I : Host.C t := {
    Host.Cfg_t := t;
    Host.Block_t := t;
    Host.H_Cfg_t := IsLink;
    Host.H_Block_t := IsLink;
    Host.run_CfgGetter_for_Self := {|
      Cfg.chain_id := chain_id;
      Cfg.spec := spec;
      Cfg.max_code_size := max_code_size;
      Cfg.is_eip3607_disabled := is_eip3607_disabled;
      Cfg.is_balance_check_disabled := is_balance_check_disabled;
      Cfg.is_gas_refund_disabled := is_gas_refund_disabled;
      Cfg.is_block_gas_limit_disabled := is_block_gas_limit_disabled;
      Cfg.is_nonce_check_disabled := is_nonce_check_disabled;
      Cfg.is_base_fee_check_disabled := is_base_fee_check_disabled;
    |};
    Host.run_Block_for_Block := {|
      Block.number := number;
      Block.beneficiary := beneficiary;
      Block.timestamp := timestamp;
      Block.gas_limit := gas_limit;
      Block.basefee := basefee;
      Block.difficulty := difficulty;
      Block.prevrandao := prevrandao;
      Block.blob_gasprice := blob_gasprice;
    |};
    Host.run_CfgGetter_for_Self := {| CfgGetter.cfg := cfg |};
    Host.run_BlockGetter_for_Self := {| BlockGetter.block := block |};
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

  Definition load_account_delegated (self : t) (address : Address.t) :
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

  Instance I : Host.C t := {
    Host.Cfg_t := t;
    Host.Block_t := t;
    Host.H_Cfg_t := IsLink;
    Host.H_Block_t := IsLink;
    Host.run_CfgGetter_for_Self := {|
      Cfg.chain_id := chain_id;
      Cfg.spec := spec;
      Cfg.max_code_size := max_code_size;
      Cfg.is_eip3607_disabled := is_eip3607_disabled;
      Cfg.is_balance_check_disabled := is_balance_check_disabled;
      Cfg.is_gas_refund_disabled := is_gas_refund_disabled;
      Cfg.is_block_gas_limit_disabled := is_block_gas_limit_disabled;
      Cfg.is_nonce_check_disabled := is_nonce_check_disabled;
      Cfg.is_base_fee_check_disabled := is_base_fee_check_disabled;
    |};
    Host.run_Block_for_Block := {|
      Block.number := number;
      Block.beneficiary := beneficiary;
      Block.timestamp := timestamp;
      Block.gas_limit := gas_limit;
      Block.basefee := basefee;
      Block.difficulty := difficulty;
      Block.prevrandao := prevrandao;
      Block.blob_gasprice := blob_gasprice;
    |};
    Host.run_CfgGetter_for_Self := {| CfgGetter.cfg := cfg |};
    Host.run_BlockGetter_for_Self := {| BlockGetter.block := block |};
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

(** ** StackUnderflow Tests *)

(** Test that static_call with empty stack returns StackUnderflow *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := static_call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that static_call with only 1 element returns StackUnderflow
    (static_call needs to pop 2 values first) *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 100 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := static_call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that static_call with only 5 elements returns StackUnderflow
    (static_call pops 2, then get_memory_input_and_out_ranges pops 4 more = 6 total needed) *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};     (* out_offset - only 5 values *)
    {| Uint.value := 0 |};     (* in_len *)
    {| Uint.value := 0 |};     (* in_offset *)
    {| Uint.value := 1000 |};  (* local_gas_limit *)
    {| Uint.value := 42 |}     (* to address *)
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := static_call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** Tests requiring full path (FatalExternalError, CallOrCreate)
    These tests go through get_memory_input_and_out_ranges which involves
    complex computation. *)

(** Test that static_call with 6 elements but no account returns FatalExternalError *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};     (* out_len *)
    {| Uint.value := 0 |};     (* out_offset *)
    {| Uint.value := 0 |};     (* in_len *)
    {| Uint.value := 0 |};     (* in_offset *)
    {| Uint.value := 1000 |};  (* local_gas_limit *)
    {| Uint.value := 42 |}     (* to address *)
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := static_call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.FatalExternalError.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that static_call with valid account returns CallOrCreate *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};     (* out_len *)
    {| Uint.value := 0 |};     (* out_offset *)
    {| Uint.value := 0 |};     (* in_len *)
    {| Uint.value := 0 |};     (* in_offset *)
    {| Uint.value := 1000 |};  (* local_gas_limit *)
    {| Uint.value := 42 |}     (* to address *)
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHostWithAccount.t := TestHostWithAccount.Make in
  let '(result_interpreter, _) := static_call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.CallOrCreate.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.
