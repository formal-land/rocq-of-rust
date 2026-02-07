Require Import simulate.RocqOfRust.
Require Import alloc.simulate.boxed.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.simulate.address.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import core.ops.simulate.range.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.instructions.links.contract.extstaticcall.
Require Import revm.revm_interpreter.instructions.simulate.contract.extcall_gas_calc.
Require Import revm.revm_interpreter.instructions.simulate.contract.extcall_input.
Require Import revm.revm_interpreter.instructions.simulate.contract.pop_extcall_target_address.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.simulate.lib.

Definition extstaticcall
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  (* require_eof! *)
  if negb (IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
      .(RuntimeFlag.is_eof) interpreter.(Interpreter.runtime_flag)) then
    let control :=
      IInterpreterTypes
          .(InterpreterTypes.LoopControl_for_Control)
          .(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.EOFOpcodeDisabledInLegacy in
    let interpreter :=
      interpreter
        <| Interpreter.control := control |> in
    (interpreter, host)
  else

  match pop_extcall_target_address interpreter with
  | (None, interpreter) => (interpreter, host)
  | (Some target_address, interpreter) =>

  match extcall_input interpreter with
  | (None, interpreter) => (interpreter, host)
  | (Some input, interpreter) =>

  match extcall_gas_calc interpreter host target_address false with
  | (None, interpreter, host) => (interpreter, host)
  | (Some gas_limit, interpreter, host) =>

  let control :=
    IInterpreterTypes
        .(InterpreterTypes.LoopControl_for_Control)
        .(LoopControl.set_next_action)
      interpreter.(Interpreter.control)
      (interpreter_action.InterpreterAction.NewFrame
        (interpreter_action.FrameInput.Call
          (Impl_Box.new
            {|
              call_inputs.CallInputs.bytecode_address := target_address;
              call_inputs.CallInputs.caller :=
                IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.target_address) interpreter.(Interpreter.input);
              call_inputs.CallInputs.gas_limit := gas_limit;
              call_inputs.CallInputs.input := input;
              call_inputs.CallInputs.is_eof := true;
              call_inputs.CallInputs.is_static := true;
              call_inputs.CallInputs.return_memory_offset :=
                @Range.Build_t usize {| Integer.value := 0 |} {| Integer.value := 0 |};
              call_inputs.CallInputs.scheme := call_inputs.CallScheme.ExtStaticCall;
              call_inputs.CallInputs.target_address := target_address;
              call_inputs.CallInputs.value := call_inputs.CallValue.Transfer Impl_Uint.ZERO
            |}
      )))
      instruction_result.InstructionResult.CallOrCreate in
  let interpreter :=
    interpreter <| Interpreter.control := control |> in

  (interpreter, host)
  end end end.

Lemma extstaticcall_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (run_Host_for_H : Host.Run H H_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (IHost : Host.C H H_types)
    (HostEq : Host.Eq.t IHost)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    SimulateM.eval_f (
      run_extstaticcall
        run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host
      )
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      let (interpreter, host) := extstaticcall interpreter host in
      [interpreter; host]%stack
    )
  }}.
Proof.
Admitted.
