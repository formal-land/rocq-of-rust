Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.links.cmp.
Require Import core.simulate.cmp.
Require Import core.simulate.option.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.bitwise.lt.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.links.lib.
Require Import ruint.simulate.cmp.
Require Import ruint.simulate.from.

Definition op_lt
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  popn_top_macro interpreter {| Integer.value := 1 |} id (fun arr top interpreter =>
    let '⟬ op1 ⟭ := arr.(array.value) in
    let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
    let result :=
      if PartialOrd.lt op1 op2 then
        {| Uint.value := 1 |}
      else
        {| Uint.value := 0 |} in
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack) result in
    interpreter
      <| Interpreter.stack := stack |>
  ).

Lemma op_lt_eq
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
      (run_lt run_InterpreterTypes_for_WIRE context)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        op_lt interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  with_strategy transparent [run_lt] unfold op_lt, run_lt; cbn.
  popn_top_macro_eq InterpreterTypesEq.
  eapply Run.Call; [
    eapply Impl_Option.unwrap_unchecked_eq;
    reflexivity
  |].
  cbn.
  match goal with
  | array : array.t aliases.U256.t _ |- _ =>
    destruct array as [[op1 []]]
  end.
  s. { s_apply @PartialOrd.Eq.lt. }
  s. { s_apply Impl_Uint.from_eq. }
  s.
Qed.
