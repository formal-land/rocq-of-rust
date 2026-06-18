Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.host.selfbalance.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.

Definition selfbalance
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  check_macro interpreter SpecId.ISTANBUL
    (fun interpreter => (interpreter, host))
    (fun interpreter =>
  gas_macro interpreter constants.LOW
    (fun interpreter => (interpreter, host))
    (fun interpreter =>
  let target :=
    IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.target_address)
      interpreter.(Interpreter.input) in
  let '(balance_opt, host) := IHost.(Host.balance) host target in
  match balance_opt with
  | None =>
    let control :=
      IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.FatalExternalError in
    (interpreter <| Interpreter.control := control |>, host)
  | Some balance =>
  push_macro interpreter balance.(StateLoad.data)
    (fun interpreter => (interpreter, host))
    (fun interpreter => (interpreter, host))
  end)).

Lemma selfbalance_eq
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
  let result := selfbalance interpreter host in
  {{
    SimulateM.eval_f
      (run_selfbalance run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
  with_strategy transparent [run_selfbalance] unfold selfbalance, run_selfbalance; cbn.
  check_macro_eq InterpreterTypesEq.
  gas_macro_eq idtac.
  s. {
    apply InterpreterTypesEq.
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
  push_macro_eq InterpreterTypesEq.
  s.
Qed.
