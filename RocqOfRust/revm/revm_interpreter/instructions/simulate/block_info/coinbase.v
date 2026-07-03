Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.bits.simulate.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import core.convert.simulate.mod.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.instructions.links.block_info.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.links.lib.

Definition coinbase
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  let '(beneficiary, host) := IHost.(Host.beneficiary) host in
  let beneficiary := Impl_From_FixedBytes_32_for_U256.from (Impl_Address.into_word beneficiary) in
  push_macro interpreter
    beneficiary
    (fun interpreter => (interpreter, host)) (fun interpreter =>
  (interpreter, host)
  ).

Lemma coinbase_eq
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
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_host : '&mut H := make_ref 1 in
  let context := {|
    instruction_context.InstructionContext.interpreter := ref_interpreter;
    instruction_context.InstructionContext.host := ref_host;
  |} in
  {{
    SimulateM.eval_f
      (run_coinbase run_InterpreterTypes_for_WIRE run_Host_for_H context)
      ([interpreter; host]%stack) 🌲
    (
      Output.Success tt,
      let '(interpreter, host) := coinbase interpreter host in
      [interpreter; host]%stack
    )
  }}.
Proof.
  intros.
  with_strategy transparent [run_coinbase] unfold coinbase, run_coinbase; cbn.
  destruct (IHost.(Host.beneficiary) host) as [beneficiary host'] eqn:?; cbn.
  apply Run.LetUnfold.
  eapply Run.Call.
  {
    s. {
      eapply (Host.Eq.beneficiary (t := HostEq)).
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
  { s. }
Qed.
