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
Require Import revm.revm_interpreter.instructions.links.control.jump_inner.
Require Import revm.revm_interpreter.interpreter.links.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.cmp.
Require Import ruint.links.from.
Require Import ruint.links.lib.

(*
pub fn jumpi<WIRE: InterpreterTypes, H: ?Sized>(context: InstructionContext<'_, H, WIRE>)
*)
Instance run_jumpi
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (context : InstructionContext.t H WIRE WIRE_types) :
  Run.Trait
    instructions.control.jumpi [] [ Φ WIRE; Φ H ] [ φ context ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_StackTrait_for_Stack. 
  destruct run_LoopControl_for_Control.
  destruct run_Jumps_for_Bytecode.
  run_symbolic.
  all: try eapply run_jump_inner.
  all: try eapply Impl_Interpreter.run_halt_underflow.
Defined.
Global Opaque run_jumpi.
