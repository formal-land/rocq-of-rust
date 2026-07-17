Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.simulate.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import core.convert.simulate.mod.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.instructions.links.tx_info.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.instructions.simulate.utility.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.

Definition origin
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  let '(caller, host) := IHost.(Host.caller) host in
  let value := Impl_IntoU256_for_Address.into_u256 caller in
  push_macro interpreter value
    (fun interpreter => (interpreter, host))
    (fun interpreter => (interpreter, host)).

Lemma origin_eq
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
  let result := origin interpreter host in
  {{
    SimulateM.eval_f
      (run_origin run_InterpreterTypes_for_WIRE run_Host_for_H context)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
  intros.
  subst result.
  with_strategy transparent [run_origin] unfold origin, run_origin; cbn.
  destruct (IHost.(Host.caller) host) as [caller host_after] eqn:?; cbn.
  apply Run.LetUnfold.
  eapply Run.Call.
  {
    s. {
      eapply (Host.Eq.caller (t := HostEq)).
    }
    s.
  }
  rewrite Heqp; cbn.
  s. {
    apply Impl_Address.into_word_eq; repeat unshelve econstructor.
  }
  s. {
    apply Impl_Into_for_From_T.Eq.I.
  }
  push_macro_eq InterpreterTypesEq.
  s.
Qed.
