Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.ops.simulate.deref.
Require Import core.simulate.array.
Require Import core.simulate.option.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.memory.mstore.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.interpreter.simulate.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import revm.revm_specification.simulate.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.bytes.
Require Import ruint.simulate.from.
Require Import ruint.simulate.lib.

Definition mstore
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{IInterpreterTypes : !InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  popn_macro interpreter 2 id (fun arr interpreter =>
  let '⟬ offset; value ⟭ := arr.(array.value) in
  as_usize_or_fail_ret_macro interpreter offset None id (fun offset interpreter =>
  resize_memory_macro interpreter offset 32 id (fun interpreter =>
  let memory :=
    IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.set)
      interpreter.(Interpreter.memory)
      offset
      (ArrayPairs.to_list (Impl_Uint.to_be_bytes value).(array.value)) in
  interpreter <| Interpreter.memory := memory |>
  )))).

Lemma mstore_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_host : '&mut H := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_mstore run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        mstore interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  with_strategy transparent [run_mstore] unfold mstore, run_mstore; cbn.
  gas_macro_eq idtac.
  popn_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t aliases.U256.t _ |- _ =>
    destruct array as [[offset [value []]]]
  end.
  as_usize_or_fail_macro_eq InterpreterTypesEq.
  resize_memory_macro_eq InterpreterTypesEq.
  s. {
    s_apply Impl_Uint.to_be_bytes_eq.
  }
  s. {
    set (ref_array := Ref.cast_to _ _).
    eapply (array.pointer_coercion_unsize_array_to_slice_eq ref_array _);
      repeat unshelve econstructor.
  }
  s. {
    apply InterpreterTypesEq.
  }
  s.
  now destruct IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.resize).
Qed.
