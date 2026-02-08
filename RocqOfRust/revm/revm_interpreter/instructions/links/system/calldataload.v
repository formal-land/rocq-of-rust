Require Import links.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.utils.links.mod.
Require Import core.array.links.mod.
Require Import core.convert.links.mod.
Require Import core.convert.links.num.
Require Import core.intrinsics.links.mod.
Require Import core.links.array.
Require Import core.links.cmp.
Require Import core.links.option.
Require Import core.links.panicking.
Require Import core.links.result.
Require Import core.ops.links.range.
Require Import core.num.links.mod.
Require Import core.ptr.links.const_ptr.
Require Import core.slice.links.index.
Require Import core.slice.links.mod.
Require Import revm.revm_interpreter.gas.links.calc.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.instructions.system.
Require Import revm.revm_interpreter.interpreter.links.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_primitives.links.lib.
Require Import revm.revm_specification.links.hardfork.
Require Import ruint.links.from.
Require Import ruint.links.lib.

Instance run_calldataload
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
  (_host : '&mut H) :
  Run.Trait
    instructions.system.calldataload [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_InputsTrait_for_Input.
  destruct Impl_TryFrom_u64_for_usize.run.
  destruct (Impl_DerefMut_for_FixedBytes_N.run {| Integer.value := 32 |}).
  destruct (Impl_Into_for_From_T.run Impl_From_FixedBytes_32_for_U256.run).
  destruct Impl_Ord_for_usize.run.
  run_symbolic.
Defined.
Global Opaque run_calldataload.
