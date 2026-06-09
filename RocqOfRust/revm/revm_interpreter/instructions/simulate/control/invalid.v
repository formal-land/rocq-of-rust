Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.control.invalid.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import revm.revm_specification.simulate.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.cmp.
Require Import ruint.simulate.from.
Require Import ruint.simulate.lib.

Definition invalid
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  let control :=
    IInterpreterTypes
      .(InterpreterTypes.LoopControl_for_Control)
      .(LoopControl.set_instruction_result)
      interpreter.(Interpreter.control)
      instruction_result.InstructionResult.InvalidFEOpcode in
  interpreter <| Interpreter.control := control |>.

Lemma invalid_eq
    {WIRE HostT : Set} `{Link WIRE} `{Link HostT}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : HostT) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_host : '&mut HostT := make_ref 1 in
  let context : Value.t :=
    Value.StructRecord
      "revm_interpreter::instruction_context::InstructionContext"
      []
      [Φ HostT; Φ WIRE]
      [
        ("interpreter", φ ref_interpreter);
        ("host", φ ref_host)
      ] in
  {{
    SimulateM.eval_f
      (run_invalid
        (WIRE := WIRE)
        (H := HostT)
        run_InterpreterTypes_for_WIRE
        context)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [invalid interpreter; _host]%stack
    )
  }}.
Proof.
Admitted.