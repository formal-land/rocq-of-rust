Require Import RocqOfRust.RocqOfRust.
Require Import links.RocqOfRust.
Require Import core.links.cmp.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.instructions.bitwise.
Require Import ruint.links.cmp.
Require Import ruint.links.from.
Require Import ruint.links.lib.

Instance run_lt
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
    (_host : '&mut H) :
  Run.Trait
    instructions.bitwise.lt [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_lt.
