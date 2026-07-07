Require Import RocqOfRust.RocqOfRust.
Require Import links.RocqOfRust.
Require Import core.convert.links.num.
Require Import core.links.cmp.
Require Import core.links.option.
Require Import core.links.result.
Require Import core.num.links.error.
Require Import core.num.links.mod.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.instructions.bitwise.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.bits.
Require Import ruint.links.cmp.
Require Import ruint.links.from.
Require Import ruint.links.lib.

Instance run_bitwise_clz
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (context : InstructionContext.t H WIRE WIRE_types) :
  Run.Trait
    instructions.bitwise.clz [] [ Φ WIRE; Φ H ] [ φ context ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct (TryFrom_usize_for_Uint.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  run_symbolic.
  { eapply Impl_Interpreter.run_halt_not_activated. }
  { eapply Impl_Interpreter.run_halt_underflow. }
Defined.
Global Opaque run_bitwise_clz.
