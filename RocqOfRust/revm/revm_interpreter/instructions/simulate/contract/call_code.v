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
Require Import revm.revm_interpreter.instructions.links.contract.call_code.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import ruint.simulate.cmp.
Require Import ruint.simulate.from.
Require Import ruint.simulate.lib.

Definition call_code
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  popn_macro interpreter {| Integer.value := 3 |}
    (fun interpreter => (interpreter, host)) (fun arr interpreter =>
  let '⟬ local_gas_limit; to; value ⟭ := arr.(array.value) in
  let to := Impl_Address.from_word (Impl_From_U256_for_FixedBytes_32.from to) in

  let local_gas_limit :=
    Impl_Result_T_E.unwrap_or
      (TryFrom_Uint_for_u64.try_from local_gas_limit)
      Impl_u64.MAX in

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

  let load := load <| AccountLoad.is_empty := false |> in
  let has_transfer := negb (Impl_Uint.is_zero value) in
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
              call_inputs.CallInputs.is_static :=
                IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.is_static) interpreter.(Interpreter.runtime_flag);
              call_inputs.CallInputs.return_memory_offset := return_memory_offset;
              call_inputs.CallInputs.scheme := call_inputs.CallScheme.CallCode;
              call_inputs.CallInputs.target_address :=
                IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.target_address) interpreter.(Interpreter.input);
              call_inputs.CallInputs.value := call_inputs.CallValue.Transfer value
            |}
      )))
      instruction_result.InstructionResult.CallOrCreate in
  let interpreter :=
    interpreter <| Interpreter.control := control |> in

  (interpreter, host)
  ) end end end).

Lemma call_code_eq
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
      run_call_code
        run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host
      )
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      let (interpreter, host) := call_code interpreter host in
      [interpreter; host]%stack
    )
  }}.
Proof.
  intros.
  with_strategy transparent [run_call_code] unfold call_code, run_call_code; cbn.
  popn_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t _ {| Integer.value := 3 |} |- _ =>
    destruct array as [[local_gas_limit [to [value []]]]]
  end.
  l. {
    cw Impl_From_U256_for_FixedBytes_32.from_eq.
    cw Impl_Address.from_word_eq.
    p.
  }
  l. {
    cw TryFrom_Uint_for_u64.try_from_eq.
    cw Impl_u64.max_eq.
    cw @Impl_Result_T_E.unwrap_or_eq.
    p.
  }
  cw @call_helpers.get_memory_input_and_out_ranges_eq.
  destruct get_memory_input_and_out_ranges as [[[input_data return_memory_offset]|] ?interpreter];
    r; [|p].
  cw HostEq.
  lu.
  destruct _.(Host.load_account_delegated) as [[load|] ?host]; cbn. 2: {
    lu.
    cw InterpreterTypesEq.
    p.
  }
  lu.
  cw @Impl_Uint.is_zero_eq.
  s. {
    apply call_helpers.calc_call_gas_eq; typeclasses eauto.
  }
  lu.
  destruct call_helpers.calc_call_gas as [[gas_limit|] ?interpreter]; r; [|p].
  gas_macro_eq idtac.
  s. {
    apply Impl_Uint.is_zero_eq; repeat unshelve econstructor.
  }
  s.
  destruct Impl_Uint.is_zero; r.
  2: s; [
    apply Impl_u64.saturating_add_eq
  |].
  all:
    lu;
    cw InterpreterTypesEq;
    cw InterpreterTypesEq;
    cw InterpreterTypesEq;
    cw @Impl_Box.new_eq;
    cw InterpreterTypesEq;
    p.
Qed.
