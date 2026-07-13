Require Import links.RocqOfRust.
Require Import alloc.links.alloc.
Require Import alloc.vec.links.mod.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.log.links.mod.
Require Import bytes.links.bytes.
Require Import core.array.links.iter.
Require Import core.convert.links.mod.
Require Import core.convert.links.num.
Require Import core.iter.adapters.links.map.
Require Import core.links.cmp.
Require Import core.links.option.
Require Import core.links.result.
Require Import core.num.links.mod.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_interpreter.gas.links.calc.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.instructions.host.
Require Import revm.revm_interpreter.instructions.links.utility.
Require Import revm.revm_interpreter.interpreter.links.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.bytes.
Require Import ruint.links.from.
Require Import ruint.links.lib.


(*
pub fn log<const N: usize, H: Host + ?Sized>(
    context: InstructionContext<'_, H, impl InterpreterTypes>,
)
*)
Instance run_log
    {N : usize}
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (run_Host_for_H : Host.Run H H_types)
    (context : InstructionContext.t H WIRE WIRE_types) :
  Run.Trait
    instructions.host.log [ φ N ] [ Φ H; Φ WIRE ] [ φ context ]
    unit.
Proof.
  constructor.
  pose proof run_InterpreterTypes_for_WIRE as run_InterpreterTypes_for_WIRE_copy.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  pose proof run_MemoryTrait_for_Memory as run_MemoryTrait_for_Memory_copy.
  destruct run_MemoryTrait_for_Memory.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_InputsTrait_for_Input.
  destruct run_LoopControl_for_Control.
  destruct run_LoopControl_for_Bytecode.
  destruct run_Host_for_H.
  destruct (Impl_AsRef_for_Slice.run u8).
  destruct run_Deref_for_Synthetic.
  destruct (
    let U256 := Uint.t {| Integer.value := 256 |} {| Integer.value := 4 |} in
    let B := FixedBytes.t {| Integer.value := 32 |} in
    let I := IntoIter.t U256 N in
    let F := Function1.t U256 B in
    Impl_Iterator_for_Map.run B I F
  ).
  destruct (
    array.links.iter.Impl_Iterator_for_IntoIter.run
      (Uint.t {| Integer.value := 256 |} {| Integer.value := 4 |})
      N
  ).
  destruct (
    Impl_IntoIterator_for_Array.run
      (Uint.t {| Integer.value := 256 |} {| Integer.value := 4 |})
      N
  ).
  destruct Impl_From_U256_for_FixedBytes_32.run.
  run_symbolic.
  all: try eapply run_resize_memory.
  all: try exact run_MemoryTrait_for_Memory_copy.
  all: try eapply method_map0.(iterator.Iterator.run_map).
  progress change
    (Value.Closure (existS (_, _) (method_from.(From.from) [] [])))
    with (φ (Function1.of_run method_from.(From.run_from))).
  destruct method_map0 as [? ? run_map].
  cbn in *.
  epose proof (
    run_map' :=
      run_map
        (FixedBytes.t {| Integer.value := 32 |})
        (Function1.t
          aliases.U256.t
          (FixedBytes.t {| Integer.value := 32 |}))
        _ _
        value_inter2
        (Function1.of_run method_from.(From.run_from))
  ).
  exact run_map'.
Defined.
Global Opaque run_log.
