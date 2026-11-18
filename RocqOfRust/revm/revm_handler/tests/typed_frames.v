Require Import simulate.RocqOfRust.
From Stdlib Require Import List String.
Require Import alloc.links.boxed.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import core.links.result.
Require Import core.ops.links.range.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_context.journal.simulate.inner.
Require Import revm.revm_context.simulate.context.
Require Import revm.revm_context.simulate.host.
Require Import revm.revm_context.simulate.journal.
Require Import revm.revm_context.tests.journal_load.
Require Import revm.revm_context_interface.links.cfg.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.context.
Require Import revm.revm_handler.simulate.evm.
Require Import revm.revm_handler.simulate.frame.
Require Import revm.revm_handler.simulate.frame_data.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.interpreter_action.links.create_inputs.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.interpreter_InterpreterResult.
Require Import revm.revm_interpreter.simulate.eth_interpreter.
Require Import revm.revm_interpreter.simulate.eth_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_state.simulate.account_info.
Require Import revm.revm_state.simulate.lib.
Require Import revm.revm_state.simulate.types.
Require Import ruint.links.lib.

Import ListNotations.
Module DbTest := journal_load.Test.
Module ContractBytecode := revm.revm_bytecode.links.bytecode.Bytecode.
#[local] Existing Instance DbTest.db_methods.

Module Test.
  Definition caller : Address.t := {| Address.value := 100 |}.

  Definition initial : Context.t DbTest.Db unit :=
    let ctx := Impl_Context.new DbTest.db SpecId.OSAKA in
    ctx <| Context.journaled_state := ctx.(Context.journaled_state) <| Journal.inner :=
      ctx.(Context.journaled_state).(Journal.inner) <| JournalInner.state :=
        [(caller, Impl_Default_for_Account.default); (DbTest.target, Impl_Default_for_Account.default)] |> |> |>.

  #[local] Instance no_precompiles : PrecompileProvider.C DbTest.Db unit := {|
    PrecompileProvider.run ctx _ _ := Some (Result.Ok None, ctx);
  |}.

  Definition empty_memory : Memory.t := {| Memory.value := []; Memory.shared_buffer := [] |}.

  Definition inputs (code : list Z) : CallInputs.t := {|
    CallInputs.input := CallInput.Bytes Impl_Bytes.new;
    CallInputs.return_memory_offset := {| Range.start := (0 : usize); Range.end_ := (0 : usize) |};
    CallInputs.gas_limit := 100000;
    CallInputs.bytecode_address := DbTest.target;
    CallInputs.known_bytecode := Some (alloy_primitives.bits.simulate.fixed.FixedBytes.from_Z 0,
      {| ContractBytecode.original_bytes := Impl_Bytes.copy_from_slice (List.map (fun byte => {| Integer.value := byte |}) code) |});
    CallInputs.target_address := DbTest.target;
    CallInputs.caller := caller;
    CallInputs.value := CallValue.Transfer (DbTest.word 0);
    CallInputs.scheme := CallScheme.Call;
    CallInputs.is_static := false;
  |}.

  Definition execute (code : list Z) :=
    ExecutionLoop.run_exec_loop 100 {| Evm.ctx := initial; Evm.frame_stack := [] |}
      {| FrameInit.depth := 0; FrameInit.memory := empty_memory;
         FrameInit.frame_input := FrameInput.Call {| Box.value := inputs code |} |}.

  Definition stored (ctx : Context.t DbTest.Db unit) :=
    match EvmState.get DbTest.target ctx.(Context.journaled_state).(Journal.inner).(JournalInner.state) with
    | None => None
    | Some account => option_map EvmStorageSlot.present_value (EvmStorage.get (DbTest.word 2) account.(Account.storage))
    end.

  Example storage_program_commits_and_charges_cold_then_warm_gas :
    match execute [96; 9; 96; 2; 85; 96; 2; 84; 0] with
    | Some (Result.Ok result, evm, fuel) => Some
        ((FrameResult.into_interpreter_result result).(InterpreterResult.result),
        (FrameResult.into_interpreter_result result).(InterpreterResult.gas).(Gas.remaining).(Integer.value),
        stored evm.(Evm.ctx), List.length evm.(Evm.frame_stack),
        evm.(Evm.ctx).(Context.journaled_state).(Journal.inner).(JournalInner.depth).(Integer.value),
        evm.(Evm.ctx).(Context.journaled_state).(Journal.database).(DbTest.reads))
    | _ => None
    end = Some (InstructionResult.Stop, 94891, Some (DbTest.word 9), 0%nat, 0, [DbTest.Storage]).
  Proof. vm_compute. reflexivity. Qed.

  Example reverting_program_restores_storage :
    match execute [96; 9; 96; 2; 85; 95; 95; 253] with
    | Some (Result.Ok result, evm, _) => Some
        ((FrameResult.into_interpreter_result result).(InterpreterResult.result), stored evm.(Evm.ctx),
          evm.(Evm.ctx).(Context.journaled_state).(Journal.inner).(JournalInner.depth).(Integer.value))
    | _ => None
    end = Some (InstructionResult.Revert, Some (DbTest.word 7), 0).
  Proof. vm_compute. reflexivity. Qed.

  Example call_depth_failure_does_not_create_a_checkpoint :
    match Impl_EthFrame.make_call_frame initial 1025 empty_memory (inputs [0]) with
    | Some (Result.Ok (ItemOrResult.Result result), ctx) => Some
        ((FrameResult.into_interpreter_result result).(InterpreterResult.result), ctx)
    | _ => None
    end = Some (InstructionResult.CallTooDeep, initial).
  Proof. vm_compute. reflexivity. Qed.

  Example bytecode_database_error_retains_checkpoint_and_database_read :
    let ctx := initial <| Context.journaled_state := initial.(Context.journaled_state)
      <| Journal.database := DbTest.db <| DbTest.fail_basic := true |> |> |> in
    let call_inputs := (inputs [0]) <| CallInputs.known_bytecode := None |>
      <| CallInputs.bytecode_address := {| Address.value := 123 |} |> in
    match Impl_EthFrame.make_call_frame ctx 0 empty_memory call_inputs with
    | Some (Result.Err (ContextError.Db _), ctx) => Some
        (ctx.(Context.journaled_state).(Journal.database).(DbTest.reads),
          ctx.(Context.journaled_state).(Journal.inner).(JournalInner.depth).(Integer.value))
    | _ => None
    end = Some ([DbTest.Basic], 1).
  Proof. vm_compute. reflexivity. Qed.
  Definition slot_value (ctx : Context.t DbTest.Db unit) (address : Address.t) (key : Z) :=
    match EvmState.get address ctx.(Context.journaled_state).(Journal.inner).(JournalInner.state) with
    | None => None
    | Some account => option_map EvmStorageSlot.present_value (EvmStorage.get (DbTest.word key) account.(Account.storage))
    end.

  Example nested_revert_restores_child_storage_and_returns_failure_to_parent :
    let child_code := Impl_Bytes.copy_from_slice
      (List.map (fun byte => {| Integer.value := byte |}) [96; 9; 96; 2; 85; 95; 95; 253]) in
    let info := Impl_Default_for_AccountInfo.default <| AccountInfo.code :=
      Some {| ContractBytecode.original_bytes := child_code |} |> in
    let ctx := initial <| Context.journaled_state := initial.(Context.journaled_state)
      <| Journal.database := DbTest.db <| DbTest.info := Some info |> |> |> in
    let call_inputs := inputs [95; 95; 95; 95; 95; 96; 20; 97; 255; 255; 241; 96; 3; 85; 0] in
    match ExecutionLoop.run_exec_loop 100 {| Evm.ctx := ctx; Evm.frame_stack := [] |}
      {| FrameInit.depth := 0; FrameInit.memory := empty_memory;
        FrameInit.frame_input := FrameInput.Call {| Box.value := call_inputs |} |} with
    | Some (Result.Ok result, evm, fuel) => Some
        ((FrameResult.into_interpreter_result result).(InterpreterResult.result),
          slot_value evm.(Evm.ctx) DbTest.target 3,
          slot_value evm.(Evm.ctx) {| Address.value := 20 |} 2,
          evm.(Evm.ctx).(Context.journaled_state).(Journal.inner).(JournalInner.depth).(Integer.value),
          List.length evm.(Evm.frame_stack), Nat.ltb fuel 100)
    | _ => None
    end = Some (InstructionResult.Stop, Some (DbTest.word 0), Some (DbTest.word 7), 0, 0%nat, true).
  Proof. vm_compute. reflexivity. Qed.

  Definition create_inputs : CreateInputs.t := {|
    CreateInputs.caller := caller;
    CreateInputs.scheme := CreateScheme.Create;
    CreateInputs.value := DbTest.word 0;
    CreateInputs.init_code := Impl_Bytes.copy_from_slice [(0 : u8)];
    CreateInputs.gas_limit := 100000;
  |}.

  Example create_collision_keeps_caller_nonce_bump :
    let info := Impl_Default_for_AccountInfo.default <| AccountInfo.nonce := 1 |> in
    let ctx := initial <| Context.journaled_state := initial.(Context.journaled_state)
      <| Journal.database := DbTest.db <| DbTest.info := Some info |> |> |> in
    match Impl_EthFrame.make_create_frame ctx 0 empty_memory create_inputs with
    | Some (Result.Ok (ItemOrResult.Result (FrameResult.Create result)), ctx) => Some
        (result.(CreateOutcome.result).(InterpreterResult.result), result.(CreateOutcome.address),
          option_map (fun account => account.(Account.info).(AccountInfo.nonce).(Integer.value))
            (EvmState.get caller ctx.(Context.journaled_state).(Journal.inner).(JournalInner.state)),
          ctx.(Context.journaled_state).(Journal.inner).(JournalInner.depth).(Integer.value))
    | _ => None
    end = Some (InstructionResult.CreateCollision, None, Some 1, 0).
  Proof. vm_compute. reflexivity. Qed.

  Example create_empty_contract_commits_new_account :
    let ctx := initial <| Context.journaled_state := initial.(Context.journaled_state)
      <| Journal.database := DbTest.db <| DbTest.info := None |> |> |> in
    match ExecutionLoop.run_exec_loop 100 {| Evm.ctx := ctx; Evm.frame_stack := [] |}
      {| FrameInit.depth := 0; FrameInit.memory := empty_memory;
        FrameInit.frame_input := FrameInput.Create {| Box.value := create_inputs |} |} with
    | Some (Result.Ok (FrameResult.Create result), evm, _) =>
      match result.(CreateOutcome.address) with
      | None => None
      | Some address => Some (result.(CreateOutcome.result).(InterpreterResult.result),
          option_map (fun account => (account.(Account.info).(AccountInfo.nonce).(Integer.value),
            Impl_Account.is_created account))
            (EvmState.get address evm.(Evm.ctx).(Context.journaled_state).(Journal.inner).(JournalInner.state)),
          evm.(Evm.ctx).(Context.journaled_state).(Journal.inner).(JournalInner.depth).(Integer.value))
      end
    | _ => None
    end = Some (InstructionResult.Return, Some (1, true), 0).
  Proof. vm_compute. reflexivity. Qed.
End Test.
