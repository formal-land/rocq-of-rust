Require Import simulate.RocqOfRust.
Require Import alloc.simulate.boxed.
Require Import alloy_primitives.bits.simulate.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import core.links.array.
Require Import core.num.simulate.mod.
Require Import core.simulate.result.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.contract.simulate.call_helpers.
Require Import revm.revm_interpreter.instructions.links.contract.call.
Require Import revm.revm_interpreter.instructions.links.utility.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.instructions.simulate.utility.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import revm.revm_specification.simulate.hardfork.
Require Import ruint.simulate.cmp.
Require Import ruint.simulate.from.
Require Import ruint.simulate.lib.

Definition call
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {IHost : Host.C H}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  popn_macro interpreter {| Integer.value := 3 |}
    (fun interpreter => (interpreter, host)) (fun arr interpreter =>
  let '(_, local_gas_limit, to, value) := ArrayPairs.to_tuple_rev (arr.(array.value)) in
  let to := Impl_IntoAddress_for_U256.into_address to in

  let local_gas_limit :=
    Impl_Result_T_E.unwrap_or
      (TryFrom_Uint_for_u64.try_from local_gas_limit)
      Impl_u64.MAX in

  let has_transfer := negb (Impl_Uint.is_zero value) in
  let is_static :=
    IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.is_static)
      interpreter.(Interpreter.runtime_flag) in

  if is_static && has_transfer then
    let control :=
      IInterpreterTypes
          .(InterpreterTypes.LoopControl_for_Control)
          .(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.CallNotAllowedInsideStatic in
    let interpreter :=
      interpreter
        <| Interpreter.control := control |> in
    (interpreter, host)
  else

  match call_helpers.get_memory_input_and_out_ranges interpreter with
  | (None, interpreter) => (interpreter, host)
  | (Some (input, return_memory_offset), interpreter) =>

  match IHost.(Host.load_account_delegated) host to with
  | (None, host) =>
    let control :=
      IInterpreterTypes
          .(InterpreterTypes.LoopControl_for_Control)
          .(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.FatalExternalError in
    let interpreter :=
      interpreter
        <| Interpreter.control := control |> in
    (interpreter, host)
  | (Some load, host) =>

  match call_helpers.calc_call_gas interpreter load has_transfer local_gas_limit with
  | (None, interpreter) => (interpreter, host)
  | (Some gas_limit, interpreter) =>
  gas_macro interpreter gas_limit
    (fun interpreter => (interpreter, host)) (fun interpreter =>

  let gas_limit :=
    if has_transfer then
      Impl_u64.saturating_add gas_limit CALL_STIPEND
    else
      gas_limit in

  let control :=
    IInterpreterTypes
        .(InterpreterTypes.LoopControl_for_Control)
        .(LoopControl.set_next_action)
      interpreter.(Interpreter.control)
      (interpreter_action.InterpreterAction.NewFrame
        (interpreter_action.FrameInput.Call
          (Impl_Box.new
            {|
              call_inputs.CallInputs.bytecode_address := to;
              call_inputs.CallInputs.caller :=
                IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.target_address) interpreter.(Interpreter.input);
              call_inputs.CallInputs.gas_limit := gas_limit;
              call_inputs.CallInputs.input := input;
              call_inputs.CallInputs.is_eof := false;
              call_inputs.CallInputs.is_static := is_static;
              call_inputs.CallInputs.return_memory_offset := return_memory_offset;
              call_inputs.CallInputs.scheme := call_inputs.CallScheme.Call;
              call_inputs.CallInputs.target_address := to;
              call_inputs.CallInputs.value := call_inputs.CallValue.Transfer value
            |}
      )))
      instruction_result.InstructionResult.CallOrCreate in
  let interpreter :=
    interpreter <| Interpreter.control := control |> in

  (interpreter, host)
  ) end end end).

Lemma call_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (run_Host_for_H : Host.Run H H_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (IHost : Host.C H)
    (HostEq : Host.Eq.t IHost)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    SimulateM.eval_f (
      run_call
        run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host
      )
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      let (interpreter, host) := call interpreter host in
      [interpreter; host]%stack
    )
  }}.
Proof.
Admitted.
