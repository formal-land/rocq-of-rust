Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.instructions.links.host.balance.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.instructions.simulate.utility.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import revm.revm_specification.simulate.hardfork.

Definition balance
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  popn_top_macro interpreter 0
    (fun interpreter => (interpreter, host)) (fun _ top interpreter =>
  let address :=
    Impl_IntoAddress_for_U256.into_address
      (top.(RefStub.projection) interpreter.(Interpreter.stack)) in
  let '(balance_opt, host) := IHost.(Host.balance) host address in
  match balance_opt with
  | None =>
    let control :=
      IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.FatalExternalError in
    (interpreter <| Interpreter.control := control |>, host)
  | Some balance =>
  let spec_id :=
    IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  gas_macro interpreter
    (if Impl_SpecId.is_enabled_in spec_id SpecId.BERLIN then
      calc.warm_cold_cost balance.(StateLoad.is_cold)
    else if Impl_SpecId.is_enabled_in spec_id SpecId.ISTANBUL then
      700
    else if Impl_SpecId.is_enabled_in spec_id SpecId.TANGERINE then
      400
    else
      20
    )
    (fun interpreter => (interpreter, host)) (fun interpreter =>
  let stack :=
    top.(RefStub.injection)
      interpreter.(Interpreter.stack) balance.(StateLoad.data) in
  (interpreter <| Interpreter.stack := stack |>, host))
  end).

Lemma balance_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_Host_for_H : Host.Run H H_types)
    `{IInterpreterTypes : !InterpreterTypes.C WIRE_types}
    `{InterpreterTypesEq :
      !InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes}
    `{IHost : !Host.C H H_types}
    `{HostEq : !Host.Eq.t IHost}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref (A := H) 1 in
  let result := balance interpreter host in
  {{
    SimulateM.eval_f
      (run_balance run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
  with_strategy transparent [run_balance] unfold balance, run_balance; cbn.
  unfold popn_top_macro.
  s. {
    apply InterpreterTypesEq.
  }
  s; destruct _.(StackTrait.popn_top) as [[[]|] ?s]; cbn. 2: {
    s. {
      apply InterpreterTypesEq.
    }
    s.
  }
  s. {
    apply Impl_IntoAddress_for_U256.into_address_eq.
  }
  s. {
    apply HostEq.
  }
  destruct _.(Host.balance) as [[balance|] ?host]; cbn. 2: {
    s. {
      apply InterpreterTypesEq.
    }
    s.
  }
  unfold gas_macro.
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply Impl_SpecId.is_enabled_in_eq.
  }
  Ltac final_block InterpreterTypesEq :=
    s; [
      apply Impl_Gas.record_cost_eq
    |];
    destruct Impl_Gas.record_cost; [s|];
    s; [
      apply InterpreterTypesEq
    |];
    s.
  destruct Impl_SpecId.is_enabled_in.
  { s. {
      apply calc.warm_cold_cost_eq.
    }
    final_block InterpreterTypesEq.
  }
  { s. {
      apply Impl_SpecId.is_enabled_in_eq.
    }
    destruct Impl_SpecId.is_enabled_in.
    { final_block InterpreterTypesEq. }
    { s. {
        apply Impl_SpecId.is_enabled_in_eq.
      }
      destruct Impl_SpecId.is_enabled_in.
      { final_block InterpreterTypesEq. }
      { final_block InterpreterTypesEq. }
    }
  }
Qed.
