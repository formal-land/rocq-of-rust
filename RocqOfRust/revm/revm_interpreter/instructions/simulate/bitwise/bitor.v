Require Import simulate.RocqOfRust.
Require Import core.links.array.
Require Import core.links.cmp.
Require Import core.ops.simulate.bit.
Require Import core.simulate.cmp.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.bitwise.bitor.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.links.lib.
Require Import ruint.simulate.bits.
Require Import ruint.simulate.cmp.
Require Import ruint.simulate.from.

Definition op_bitor
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  popn_top_macro interpreter {| Integer.value := 1 |} id (fun arr top interpreter =>
    let '{| ArrayPair.x := op1 |} := arr.(array.value) in
    let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
    let result := Impl_BitOr_for_Uint.bitor op1 op2 in
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack) result in
    interpreter
      <| Interpreter.stack := stack |>
  )).

Lemma op_bitor_eq
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
  {{
    SimulateM.eval_f
      (run_bitwise_bitor run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        op_bitor interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  unfold op_bitor.
  gas_macro_eq InterpreterTypesEq.
  popn_top_macro_eq InterpreterTypesEq.
  cbn.
  apply Run.LetUnfold.
  get_can_access.
  eapply Run.Call. {
    apply BitOr.Eq.bitor.
  }
  cbn.
  get_can_access.
  cbn.
  apply Run.PureEq; repeat f_equal.
Qed.
