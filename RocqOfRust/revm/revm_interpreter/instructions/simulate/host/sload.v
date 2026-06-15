Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.instructions.links.host.sload.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.

Definition sload
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  popn_top_macro interpreter 0
    (fun interpreter => (interpreter, host)) (fun _ index_stub interpreter =>
  let index := index_stub.(RefStub.projection) interpreter.(Interpreter.stack) in
  let target_address :=
    IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.target_address)
      interpreter.(Interpreter.input) in
  let '(value_opt, host) := IHost.(Host.sload) host target_address index in
  match value_opt with
  | None =>
    let control :=
      IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.FatalExternalError in
    (interpreter <| Interpreter.control := control |>, host)
  | Some value =>
  let spec_id :=
    IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  gas_macro interpreter
    (calc.sload_cost spec_id value.(StateLoad.is_cold))
    (fun interpreter => (interpreter, host)) (fun interpreter =>
  let stack :=
    index_stub.(RefStub.injection)
      interpreter.(Interpreter.stack)
      value.(StateLoad.data) in
  (interpreter <| Interpreter.stack := stack |>, host))
  end).

Lemma sload_eq
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
  let result := sload interpreter host in
  {{
    SimulateM.eval_f
      (run_sload run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
  with_strategy transparent [run_sload] unfold sload, run_sload; cbn.
  unfold popn_top_macro.
  s. {
    apply InterpreterTypesEq.
  }
  s; destruct _.(StackTrait.popn_top) as [[[]|] ?stack']; cbn. 2: {
    s. {
      apply InterpreterTypesEq.
    }
    s.
  }
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply HostEq.
  }
  destruct _.(Host.sload) as [[value|] ?host]; cbn. 2: {
    s. {
      apply InterpreterTypesEq.
    }
    s.
  }
  s. {
    apply InterpreterTypesEq.
  }
  unfold gas_macro.
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply calc.sload_cost_eq.
  }
  s. {
    apply Impl_Gas.record_cost_eq.
  }
  destruct Impl_Gas.record_cost; cbn.
  { s. }
  { s. {
      apply InterpreterTypesEq.
    }
    s.
  }
Qed.
