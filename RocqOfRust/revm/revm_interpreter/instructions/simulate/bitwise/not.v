Require Import simulate.RocqOfRust.
Require Import core.links.array.
Require Import core.links.cmp.
Require Import core.ops.simulate.bit.
Require Import core.simulate.cmp.
Require Import core.simulate.option.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.bitwise.not.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.links.lib.
Require Import ruint.simulate.bits.
Require Import ruint.simulate.cmp.
Require Import ruint.simulate.from.

Definition op_not
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  popn_top_macro interpreter {| Integer.value := 0 |} id (fun arr top interpreter =>
    let op1 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
    let result := Impl_Not_for_Uint.not op1 in
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack) result in
    interpreter
      <| Interpreter.stack := stack |>
  ).

Lemma op_not_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
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
      (run_bitwise_not run_InterpreterTypes_for_WIRE context)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        op_not interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  with_strategy transparent [run_bitwise_not] unfold op_not, run_bitwise_not; cbn.
  popn_top_macro_eq InterpreterTypesEq.
  eapply Run.Call; [
    eapply Impl_Option.unwrap_unchecked_eq;
    reflexivity
  |].
  cbn.
  lu.
  cw @Not.Eq.not.
  pf.
Qed.
