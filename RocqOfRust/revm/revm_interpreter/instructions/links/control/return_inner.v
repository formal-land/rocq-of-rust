Require Import links.RocqOfRust.
Require Import alloc.links.alloc.
Require Import alloc.links.slice.
Require Import alloc.vec.links.mod.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.convert.links.mod.
Require Import core.convert.links.num.
Require Import core.fmt.links.mod.
Require Import core.links.option.
Require Import core.links.panicking.
Require Import core.links.result.
Require Import core.num.links.mod.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.instructions.control.
Require Import revm.revm_interpreter.interpreter.links.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.cmp.
Require Import ruint.links.from.
Require Import ruint.links.lib.

(*
fn return_inner(
    interpreter: &mut Interpreter<impl InterpreterTypes>,
    instruction_result: InstructionResult,
)
*)
Instance run_return_inner
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
    (instruction_result : InstructionResult.t) :
  Run.Trait
    instructions.control.return_inner [] [ Φ WIRE ] [ φ interpreter; φ instruction_result ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  pose proof run_MemoryTrait_for_Memory as run_MemoryTrait_for_Memory_copy.
  destruct run_MemoryTrait_for_Memory.
  destruct run_Deref_for_Synthetic.
  destruct Impl_Default_for_Bytes.run.
  destruct (Impl_Into_for_From_T.run Impl_From_Vec_u8_for_Bytes.run).
  run_symbolic.
Defined.
Global Opaque run_return_inner.
