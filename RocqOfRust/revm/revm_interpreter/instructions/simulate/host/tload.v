Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.instructions.links.host.tload.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.

Definition tload
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  check_macro interpreter SpecId.CANCUN
    (fun interpreter => (interpreter, host)) (fun interpreter =>
  popn_top_macro interpreter 0 (fun interpreter => (interpreter, host)) (fun _ top interpreter =>
  let target :=
    IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.target_address)
      interpreter.(Interpreter.input) in
  let index := top.(RefStub.projection) interpreter.(Interpreter.stack) in
  let '(value, host) := IHost.(Host.tload) host target index in
  let stack := top.(RefStub.injection) interpreter.(Interpreter.stack) value in
  (interpreter <| Interpreter.stack := stack |>, host)
  )).

Lemma tload_eq
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
  let context := {|
    instruction_context.InstructionContext.interpreter := ref_interpreter;
    instruction_context.InstructionContext.host := ref_host;
  |} in
  let result := tload interpreter host in
  {{
    SimulateM.eval_f
      (run_tload run_InterpreterTypes_for_WIRE run_Host_for_H context)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
  intros.
  subst result.
  with_strategy transparent [run_tload] unfold tload, run_tload; cbn.
  check_macro_eq InterpreterTypesEq.
  popn_top_macro_eq InterpreterTypesEq.
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply HostEq.
  }
  s; now destruct _.(Host.tload).
Qed.
