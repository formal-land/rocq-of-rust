Require Import simulate.RocqOfRust.
Require Import alloc.simulate.boxed.
Require Import alloy_primitives.bits.simulate.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.num.simulate.mod.
Require Import core.simulate.result.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.instructions.contract.simulate.call_helpers.
Require Import revm.revm_interpreter.instructions.links.contract.delegate_call.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import ruint.simulate.from.
Require Import ruint.simulate.lib.

Definition delegate_call
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  check_macro interpreter SpecId.HOMESTEAD
    (fun interpreter => (interpreter, host)) (fun interpreter =>
  popn_macro interpreter 2
    (fun interpreter => (interpreter, host)) (fun arr interpreter =>
  let '⟬ local_gas_limit; to ⟭ := arr.(array.value) in
  let to := Impl_Address.from_word (Impl_From_U256_for_FixedBytes_32.from to) in

  let local_gas_limit :=
    Impl_Result_T_E.unwrap_or
      (TryFrom_Uint_for_u64.try_from local_gas_limit)
      Impl_u64.MAX in

  match call_helpers.get_memory_input_and_out_ranges interpreter with
  | (None, interpreter) => (interpreter, host)
  | (Some (input, return_memory_offset), interpreter) =>

  match call_helpers.load_acc_and_calc_gas
      interpreter host to false false local_gas_limit with
  | (None, interpreter, host) => (interpreter, host)
  | (Some load, interpreter, host) =>

  let bytecode :=
    IInterpreterTypes
        .(InterpreterTypes.LoopControl_for_Bytecode)
        .(LoopControl.set_action)
      interpreter.(Interpreter.bytecode)
      (interpreter_action.InterpreterAction.NewFrame
        (interpreter_action.FrameInput.Call
          (Impl_Box.new
            {|
              call_inputs.CallInputs.bytecode_address := to;
              call_inputs.CallInputs.caller :=
                IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.caller_address) interpreter.(Interpreter.input);
              call_inputs.CallInputs.gas_limit := load.(call_helpers.LoadAccAndCalcGasResult.gas_limit);
              call_inputs.CallInputs.input := call_inputs.CallInput.SharedBuffer input;
              call_inputs.CallInputs.is_static :=
                IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.is_static) interpreter.(Interpreter.runtime_flag);
              call_inputs.CallInputs.known_bytecode :=
                Some (
                  load.(call_helpers.LoadAccAndCalcGasResult.bytecode_hash),
                  load.(call_helpers.LoadAccAndCalcGasResult.bytecode)
                );
              call_inputs.CallInputs.return_memory_offset := return_memory_offset;
              call_inputs.CallInputs.scheme := call_inputs.CallScheme.DelegateCall;
              call_inputs.CallInputs.target_address :=
                IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.target_address) interpreter.(Interpreter.input);
              call_inputs.CallInputs.value :=
                call_inputs.CallValue.Apparent
                  (IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.call_value) interpreter.(Interpreter.input))
            |}
      ))) in
  let interpreter :=
    interpreter <| Interpreter.bytecode := bytecode |> in

  (interpreter, host)
  end end)).

Lemma delegate_call_eq
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
      run_delegate_call
        run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host
      )
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      let (interpreter, host) := delegate_call interpreter host in
      [interpreter; host]%stack
    )
  }}.
Proof.
Admitted.
