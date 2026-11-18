Require Import simulate.RocqOfRust.
From Stdlib Require Import List String.
Require Import core.links.result.
Require Import core.ops.links.range.
Require Import revm.revm_context.simulate.context.
Require Import revm.revm_context.simulate.journal.
Require Import revm.revm_context.simulate.local.
Require Import revm.revm_context.journal.simulate.inner.
Require Import revm.revm_context_interface.simulate.execution_result.
Require Import revm.revm_handler.simulate.handler.
Require Import revm.revm_handler.simulate.precompile_provider.
Require Import revm.revm_handler.tests.typed_frames.
Require Import revm.revm_handler.tests.typed_handler.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_InterpreterResult.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.simulate.eth_types.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.links.common.
Require Import revm.revm_context.simulate.tx.

#[local] Existing Instance journal_load.Test.db_methods.
#[local] Existing Instance EthPrecompiles.methods.

Module Test.
  Definition ctx (address : Z) :=
    let ctx := typed_handler.Test.initial [] in
    ctx <| Context.tx := ctx.(Context.tx) <| TxEnv.kind := TxKind.Call {| Address.value := address |} |> |>.

  Example identity_runs_through_the_transaction_handler :
    let ctx := ctx 4 in
    let ctx := ctx <| Context.tx := ctx.(Context.tx) <| TxEnv.data := typed_handler.Test.bytes [1; 2; 3] |> |> in
    match Handler.run 100 (EthPrecompiles.warm_addresses hardfork.SpecId.OSAKA) ctx with
    | Some (Result.Ok result, _) => Some result
    | _ => None
    end = Some (ExecutionResult.Success SuccessReason.Return 21120 0 []
      (Output.Call (typed_handler.Test.bytes [1; 2; 3]))).
  Proof. vm_compute. reflexivity. Qed.

  Example top_level_precompile_error_carries_rust_message :
    match Handler.run 100 (EthPrecompiles.warm_addresses hardfork.SpecId.OSAKA) (ctx 9) with
    | Some (Result.Ok result, _) => Some result
    | _ => None
    end = Some (ExecutionResult.Halt
      (HaltReason.PrecompileErrorWithContext "wrong input length for blake2"%string) 100000).
  Proof. vm_compute. reflexivity. Qed.

  Example nested_precompile_error_does_not_set_top_level_message :
    let ctx := typed_frames.Test.initial in
    let ctx := ctx <| Context.journaled_state := ctx.(Context.journaled_state)
      <| Journal.inner := ctx.(Context.journaled_state).(Journal.inner) <| JournalInner.depth := 2 |> |> |> in
    let inputs := (typed_frames.Test.inputs []) <| CallInputs.bytecode_address := {| Address.value := 9 |} |> in
    match EthPrecompiles.run ctx typed_frames.Test.empty_memory inputs with
    | Some (Result.Ok (Some result), ctx) => Some (result.(InterpreterResult.result),
      ctx.(Context.local).(LocalContext.precompile_error_message))
    | _ => None
    end = Some (InstructionResult.PrecompileError, None).
  Proof. vm_compute. reflexivity. Qed.

  Example shared_input_checks_bounds_before_converting_offsets :
    EthPrecompiles.input_bytes typed_frames.Test.empty_memory
      (CallInput.SharedBuffer {| Range.start := ({| Integer.value := 2 ^ 64 - 1 |} : usize);
        Range.end_ := ({| Integer.value := 2 ^ 64 - 1 |} : usize) |}) = [].
  Proof. vm_compute. reflexivity. Qed.

  Example out_of_gas_preserves_interpreter_gas_until_frame_settlement :
    let inputs := (typed_frames.Test.inputs []) <| CallInputs.bytecode_address := {| Address.value := 4 |} |>
      <| CallInputs.gas_limit := 14 |> in
    match EthPrecompiles.run typed_frames.Test.initial typed_frames.Test.empty_memory inputs with
    | Some (Result.Ok (Some result), ctx) => Some (result.(InterpreterResult.result),
      result.(InterpreterResult.gas).(Gas.remaining).(Integer.value),
      ctx.(Context.local).(LocalContext.precompile_error_message))
    | _ => None
    end = Some (InstructionResult.PrecompileOOG, 14, None).
  Proof. vm_compute. reflexivity. Qed.
End Test.
