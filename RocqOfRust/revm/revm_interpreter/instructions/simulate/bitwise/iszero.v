Require Import simulate.RocqOfRust.
Require Import core.links.array.
Require Import core.links.cmp.
Require Import core.simulate.cmp.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.bitwise.iszero.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.links.lib.
Require Import ruint.simulate.cmp.
Require Import ruint.simulate.from.

Definition op_iszero
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  popn_top_macro interpreter {| Integer.value := 0 |} id (fun arr top interpreter =>
    let op1 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
    let result :=
      if Impl_Uint.is_zero op1 then
        {| Uint.value := 1 |}
      else
        {| Uint.value := 0 |} in
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack) result in
    interpreter
      <| Interpreter.stack := stack |>
  )).

Lemma op_iszero_eq
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
      (run_bitwise_is_zero run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        op_iszero interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
Admitted.
