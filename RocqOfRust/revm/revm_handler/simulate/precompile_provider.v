Require Import simulate.RocqOfRust.
From Stdlib Require Import List String.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import core.links.result.
Require Import core.ops.links.range.
Require Import revm.revm_context.simulate.cfg.
Require Import revm.revm_context.simulate.context.
Require Import revm.revm_context.simulate.journal.
Require Import revm.revm_context.simulate.local.
Require Import revm.revm_handler.simulate.frame.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_InterpreterResult.
Require Import revm.revm_interpreter.simulate.eth_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_precompile.simulate.interface.
Require Import revm.revm_precompile.simulate.precompiles.


Module EthPrecompiles.
  Definition warm_addresses := EthereumPrecompiles.addresses.

  Definition input_bytes (memory : Memory.t) (input : CallInput.t) : list u8 :=
    match input with
    | CallInput.Bytes input => input.(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value)
    | CallInput.SharedBuffer range =>
      let start := range.(Range.start).(Integer.value) in
      let finish := range.(Range.end_).(Integer.value) in
      let buffer := memory.(Memory.shared_buffer) in
      if Z.leb 0 start && Z.leb start finish && Z.leb finish (Z.of_nat (List.length buffer)) then
        List.firstn (Z.to_nat (finish - start)) (List.skipn (Z.to_nat start) buffer)
      else [] (* LocalContext::shared_memory_buffer_slice returns None. *)
    end.

  Definition run {DB Error : Set} (ctx : Context.t DB Error) (memory : Memory.t) (inputs : CallInputs.t)
      : option (Result.t (option InterpreterResult.t) string * Context.t DB Error) :=
    let spec := ctx.(Context.cfg).(CfgEnv.spec) in
    if negb (EthereumPrecompiles.contains spec inputs.(CallInputs.bytecode_address)) then Some (Result.Ok None, ctx) else
    let result := {| InterpreterResult.result := InstructionResult.Return;
      InterpreterResult.gas := Impl_Gas.new inputs.(CallInputs.gas_limit);
      InterpreterResult.output := Impl_Bytes.new |} in
    match EthereumPrecompiles.execute spec inputs.(CallInputs.bytecode_address)
      (input_bytes memory inputs.(CallInputs.input)) inputs.(CallInputs.gas_limit) with
    | None => None
    | Some (Result.Ok output) =>
      let gas := Impl_Gas.record_refund result.(InterpreterResult.gas) output.(PrecompileOutput.gas_refunded) in
      match Impl_Gas.record_cost gas output.(PrecompileOutput.gas_used) with
      | None => None (* Rust asserts that a successful precompile cannot underflow gas. *)
      | Some gas => Some (Result.Ok (Some (result
          <| InterpreterResult.gas := gas |>
          <| InterpreterResult.result := if output.(PrecompileOutput.reverted) then InstructionResult.Revert else InstructionResult.Return |>
          <| InterpreterResult.output := output.(PrecompileOutput.bytes) |>)), ctx)
      end
    | Some (Result.Err (PrecompileError.Fatal message)) => Some (Result.Err message, ctx)
    | Some (Result.Err error) =>
      let is_oog := Impl_PrecompileError.is_oog error in
      let result := result <| InterpreterResult.result := if is_oog then InstructionResult.PrecompileOOG else InstructionResult.PrecompileError |> in
      let ctx := if negb is_oog && Z.eqb (Impl_Journal.depth ctx.(Context.journaled_state)).(Integer.value) 1 then
        ctx <| Context.local := Impl_LocalContext.set_precompile_error_context ctx.(Context.local)
          (Impl_PrecompileError.to_string error) |> else ctx in
      Some (Result.Ok (Some result), ctx)
    end.

  #[global] Instance methods {DB Error : Set} : PrecompileProvider.C DB Error := {|
    PrecompileProvider.run := run;
  |}.
End EthPrecompiles.
