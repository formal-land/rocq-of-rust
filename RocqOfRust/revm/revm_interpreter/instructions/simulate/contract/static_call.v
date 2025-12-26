Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import alloy_primitives.bits.simulate.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import core.links.array.
Require Import core.simulate.result.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.instructions.contract.simulate.call_helpers.
Require Import revm.revm_interpreter.instructions.links.contract.static_call.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import revm.revm_specification.simulate.hardfork.
Require Import ruint.simulate.from.

Definition static_call
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {IHost : Host.C H}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  let inject_interpreter interpreter := (interpreter, host) in

  check_macro interpreter SpecId.BYZANTIUM inject_interpreter (fun interpreter =>
  popn_macro interpreter {| Integer.value := 2 |} inject_interpreter (fun arr interpreter =>
  let '(_, to, local_gas_limit) := ArrayPairs.to_tuple_rev (arr.(array.value)) in
  let to := Impl_Address.from_word (Impl_From_U256_for_FixedBytes_32.from to) in

  let local_gas_limit :=
    Impl_Result_T_E.unwrap_or
      (TryFrom_Uint_for_u64.try_from local_gas_limit)
      {| Integer.value := (*2 ^ 64*) - 1 |} in

  match call_helpers.get_memory_input_and_out_ranges interpreter with
  | (None, interpreter) => (interpreter, host)
  | (Some (input, return_memory_offset), interpreter) =>

  match IHost.(Host.load_account_delegated) host to with
  | (None, host) =>
    let control :=
      IInterpreterTypes
          .(InterpreterTypes.Loop)
          .(Loop.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.FatalExternalError in
    let interpreter :=
      interpreter
        <| Interpreter.control := control |> in
    (interpreter, host)
  | (Some load, host) =>

  let load := load <| AccountLoad.is_empty := false |> in
  match call_helpers.calc_call_gas interpreter load false local_gas_limit with
  | (None, interpreter) => (interpreter, host)
  | (Some gas_limit, interpreter) =>
  gas_macro interpreter gas_limit (fun interpreter => (interpreter, host)) (fun interpreter =>

  (interpreter, host)
  ) end end end)).

Lemma static_call_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (run_Host_for_H : Host.Run H H_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (IHost : Host.C H)
    (HostEq : Host.Eq.t run_Host_for_H IHost)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    SimulateM.eval_f (
      run_static_call
        run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host
      )
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      let (interpreter, host) := static_call interpreter host in
      [interpreter; host]%stack
    )
  }}.
Proof.
  intros.
  destruct InterpreterTypesEq as [[] [] [] []].
  destruct HostEq as [].
  unfold run_static_call, static_call; cbn.
  check_macro_eq spec_id set_instruction_result.
  popn_macro_eq H IInterpreterTypes popn set_instruction_result.
  eapply Run.Call. {
    apply Impl_From_U256_for_FixedBytes_32.from_eq.
  }
  eapply Run.Call. {
    apply Impl_Address.from_word_eq.
  }
  eapply Run.Call. {
    apply TryFrom_Uint_for_u64.try_from_eq.
  }
  eapply Run.Call. {
    cbn.
    (* TODO: simulate the integer *)
    eapply Run.Call. {
      apply Run.Pure.
    }
    apply Run.Pure.
  }
  eapply Run.Call. {
    apply Impl_Result_T_E.unwrap_or_eq.
  }
  eapply Run.Call. {
    apply call_helpers.get_memory_input_and_out_ranges_eq.
  }
  cbn; fold @SimulateM.let_.
  destruct get_memory_input_and_out_ranges as [[[input return_memory_offset]|] ?interpreter];
    cbn;
    [| apply Run.Pure].
  get_can_access.
  eapply Run.Call. {
    apply load_account_delegated.
  }
  destruct IHost.(Host.load_account_delegated) as [[load|] ?host].
  2: {
    eapply Run.Call; [
      apply (set_instruction_result
        _
        _
        instruction_result.InstructionResult.FatalExternalError
      )
    |];
    apply Run.Pure.
  }
  cbn.
  get_can_access.
  get_can_access.
  get_can_access.
  eapply Run.Call. {
    apply call_helpers.calc_call_gas_eq.
  }
  destruct call_helpers.calc_call_gas as [[gas_limit|] ?interpreter]; cbn; [|apply Run.Pure].

  Require Import revm.revm_interpreter.simulate.gas.
  unfold gas_macro;
  eapply Run.Call; [
    apply gas
  |];
  eapply Run.Call; [
    apply Impl_Gas.record_cost_eq
  |];
  destruct Impl_Gas.record_cost;
  (
    eapply Run.Call; [
      apply Run.Pure
    |]
  );
  [|
    eapply Run.Call; [
      apply Run.Pure
    |];
    eapply Run.Call; [
      apply (set_instruction_result _ _ instruction_result.InstructionResult.OutOfGas)
    |];
    apply Run.Pure
  ].
  cbn.
  eapply Run.Call. {
    apply Run.Pure.
  }
  cbn.
  get_can_access.
  eapply Run.Call. {
    apply target_address.
  }
  cbn.
  get_can_access.
  eapply Run.Call. {
Admitted.
Global Opaque run_static_call.
