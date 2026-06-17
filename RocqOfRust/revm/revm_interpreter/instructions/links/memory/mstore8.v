Require Import links.RocqOfRust.
Require Import core.convert.links.mod.
Require Import core.links.array.
Require Import core.links.cmp.
Require Import core.links.option.
Require Import core.num.links.mod.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.links.calc.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.instructions.memory.
Require Import revm.revm_interpreter.interpreter.links.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.bits.
Require Import ruint.links.bytes.
Require Import ruint.links.from.
Require Import ruint.links.lib.

Instance run_mstore8
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (context : InstructionContext.t H WIRE WIRE_types) :
  Run.Trait
    instructions.memory.mstore8 [] [ Φ WIRE; Φ H ] [ φ context ]
    unit.
Proof.
  constructor.
  pose proof run_InterpreterTypes_for_WIRE as run_InterpreterTypes_for_WIRE_copy.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct method_popn.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_MemoryTrait_for_Memory.
  destruct method_set.
  pose proof
    (@Impl_Interpreter.run_halt_memory_oog WIRE H0 WIRE_types H2 run_InterpreterTypes_for_WIRE_copy)
    as run_halt_memory_oog_for_WIRE.
  pose proof
    (@Impl_Interpreter.run_halt_underflow WIRE H0 WIRE_types H2 run_InterpreterTypes_for_WIRE_copy)
    as run_halt_underflow_for_WIRE.
  pose proof
    (@Impl_Interpreter.run_halt WIRE H0 WIRE_types H2 run_InterpreterTypes_for_WIRE_copy)
    as run_halt_for_WIRE.
  run_symbolic.
Defined.
Global Opaque run_mstore8.
