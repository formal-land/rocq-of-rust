Require Import links.RocqOfRust.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.convert.links.mod.
Require Import core.links.cmp.
Require Import core.links.option.
Require Import core.num.links.mod.
Require Import core.ops.links.range.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_interpreter.gas.links.calc.
Require Import revm.revm_interpreter.instructions.contract.call_helpers.
Require Import revm.revm_interpreter.interpreter.links.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.

(*
pub fn resize_memory(
    interpreter: &mut Interpreter<impl InterpreterTypes>,
    offset: U256,
    len: U256,
) -> Option<Range<usize>>
*)
Instance run_resize_memory
  {WIRE : Set} `{Link WIRE}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
  (offset len : aliases.U256.t) :
  Run.Trait
    instructions.contract.call_helpers.resize_memory
    [] [Φ WIRE] [φ interpreter; φ offset; φ len]
    (option (Range.t usize)).
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_LoopControl_for_Control.
  destruct run_MemoryTrait_for_Memory.
  run_symbolic.
  all: first [
    eapply (@Impl_Interpreter.run_halt WIRE H WIRE_types H0 run_InterpreterTypes_for_WIRE)
  | eapply (@interpreter.links.shared_memory.run_resize_memory
      WIRE_types.(InterpreterTypes.Types.Memory)
      WIRE_types.(InterpreterTypes.Types.Memory_Synthetic)
      WIRE_types.(InterpreterTypes.Types.Memory_Synthetic1)
      H0.(InterpreterTypes.Types.H_Memory)
      H0.(InterpreterTypes.Types.H_Memory_Synthetic)
      H0.(InterpreterTypes.Types.H_Memory_Synthetic1)
      (run_InterpreterTypes_for_WIRE.(InterpreterTypes.run_MemoryTrait_for_Memory)))
  | eapply (@Impl_Interpreter.run_halt_memory_oog WIRE H WIRE_types H0 run_InterpreterTypes_for_WIRE)
  ].
Defined.
Global Opaque run_resize_memory.

(*
pub fn get_memory_input_and_out_ranges(
    interpreter: &mut Interpreter<impl InterpreterTypes>,
) -> Option<(Range<usize>, Range<usize>)>
*)
Instance run_get_memory_input_and_out_ranges
  {WIRE : Set} `{Link WIRE}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : '&mut (Interpreter.t WIRE WIRE_types)) :
  Run.Trait
    instructions.contract.call_helpers.get_memory_input_and_out_ranges
    [] [Φ WIRE] [φ interpreter]
    (option (Range.t usize * Range.t usize)).
Proof.
  constructor.
  destruct (Impl_Try_for_Option.run (Range.t usize)).
  destruct (Impl_FromResidual_Infallible_for_Option.run (Range.t usize * Range.t usize)).
  destruct (Impl_AsRef_for_Slice.run u8).
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_MemoryTrait_for_Memory.
  destruct run_Deref_for_Synthetic.
  run_symbolic.
  all: first [
    eapply Impl_usize.run_saturating_add
  | eapply (@Impl_Interpreter.run_halt_underflow WIRE H WIRE_types H0 run_InterpreterTypes_for_WIRE)
  ].
Defined.
Global Opaque run_get_memory_input_and_out_ranges.
