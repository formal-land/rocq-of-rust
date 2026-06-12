Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.stack.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.instructions.simulate.utility.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.links.lib.
Require Import ruint.simulate.lib.

Definition push
    (N : usize)
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  push_macro interpreter Impl_Uint.ZERO id (fun interpreter =>
  popn_top_macro interpreter 0 id (fun _arr top interpreter =>
  let slice :=
    IInterpreterTypes.(InterpreterTypes.Immediates_for_Bytecode).(Immediates.read_slice) N in
  let imm := slice.(RefStub.projection) interpreter.(Interpreter.bytecode) in
  let top_value := top.(RefStub.projection) interpreter.(Interpreter.stack) in
  let new_value := cast_slice_to_u256 imm in
  let stack := top.(RefStub.injection) interpreter.(Interpreter.stack) new_value in
  let interpreter := interpreter <| Interpreter.stack := stack |> in
  let bytecode :=
    IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode).(Jumps.relative_jump)
      interpreter.(Interpreter.bytecode) (M.cast_integer IntegerKind.Isize N) in
  interpreter <| Interpreter.bytecode := bytecode |>
  ))).

Lemma push_eq
    (N : usize)
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
      (run_push N run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        push N interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
Admitted.
