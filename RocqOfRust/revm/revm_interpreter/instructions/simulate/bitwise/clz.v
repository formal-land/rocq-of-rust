Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.links.cmp.
Require Import core.simulate.cmp.
Require Import core.simulate.option.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.bitwise.clz.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.bits.
Require Import ruint.simulate.cmp.
Require Import ruint.simulate.from.

Definition op_clz
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  check_macro interpreter SpecId.OSAKA id (fun interpreter =>
  popn_top_macro interpreter 0 id (fun arr top interpreter =>
    let op1 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
    let leading_zeros := Impl_Uint.leading_zeros op1 in
    let result : aliases.U256.t := Impl_Uint.from leading_zeros in
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack) result in
    interpreter
      <| Interpreter.stack := stack |>
  )).

Lemma op_clz_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_host : '&mut H := make_ref 1 in
  let context := {|
    instruction_context.InstructionContext.interpreter := ref_interpreter;
    instruction_context.InstructionContext.host := ref_host;
  |} in
  {{
    SimulateM.eval_f
      (run_bitwise_clz run_InterpreterTypes_for_WIRE context)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        op_clz interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  unfold op_clz.
  check_macro_eq InterpreterTypesEq.
  popn_top_macro_eq InterpreterTypesEq.
  eapply Run.Call; [
    eapply Impl_Option.unwrap_unchecked_eq;
    reflexivity
  |].
  cbn.
  lu.
  s. {
    apply Impl_Uint.leading_zeros_eq; repeat unshelve econstructor.
  }
  s. {
    apply Impl_Uint.from_eq; [typeclasses eauto | easy].
  }
  s.
Qed.
