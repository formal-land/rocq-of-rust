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
pub fn unknown<WIRE: InterpreterTypes, H: ?Sized>(context: InstructionContext<'_, H, WIRE>)
*)
Instance run_unknown
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (context : InstructionContext.t H WIRE WIRE_types) :
  Run.Trait
    instructions.control.unknown [] [ Φ WIRE; Φ H ] [ φ context ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_LoopControl_for_Control.
  run_symbolic.
  { eapply Impl_Interpreter.run_halt. }
Defined.
Global Opaque run_unknown.
