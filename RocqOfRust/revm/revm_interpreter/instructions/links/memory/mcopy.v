Require Import links.RocqOfRust.
Require Import core.convert.links.mod.
Require Import core.convert.links.num.
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

Instance run_mcopy
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (context : InstructionContext.t H WIRE WIRE_types) :
  Run.Trait
    instructions.memory.mcopy [] [ Φ WIRE; Φ H ] [ φ context ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_MemoryTrait_for_Memory.
  destruct Impl_TryFrom_u64_for_usize.run.
  destruct Impl_Ord_for_usize.run.
  run_symbolic.
  { eapply Impl_Interpreter.run_halt_not_activated. }
  { eapply Impl_Interpreter.run_halt. }
  { eapply Impl_Interpreter.run_halt_oog. }
  { eapply Impl_Interpreter.run_halt_oog. }
  { eapply Impl_Interpreter.run_halt. }
  { eapply Impl_Interpreter.run_halt. }
  { eapply Impl_Interpreter.run_halt_memory_oog. }
  { eapply Impl_Interpreter.run_halt_underflow. }
Defined.
Global Opaque run_mcopy.
