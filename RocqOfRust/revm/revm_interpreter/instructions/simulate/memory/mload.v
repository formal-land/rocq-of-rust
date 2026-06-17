Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.ops.simulate.deref.
Require Import core.simulate.option.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.memory.mload.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.interpreter.simulate.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_specification.simulate.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.bytes.
Require Import ruint.simulate.from.

Definition mload
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{IInterpreterTypes : !InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  popn_top_macro interpreter 0 id (fun _ top_stub interpreter =>
  let top := top_stub.(RefStub.projection) interpreter.(Interpreter.stack) in
  as_usize_or_fail_macro interpreter top None id (fun offset interpreter =>
  resize_memory_macro interpreter offset 32 id (fun interpreter =>
  let memory_slice :=
    IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.slice_len)
      interpreter.(Interpreter.memory) offset 32 in
  let deref_stub :=
    IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.Deref_for_Synthetic).(Deref.deref) in
  let bytes := deref_stub.(RefStub.projection) memory_slice in
  (* [Impl_Uint.try_from_be_slice_eq] in the success case *)
  let value := {| Uint.value := Impl_Uint.bytes_to_value bytes |} in
  let stack := top_stub.(RefStub.injection) interpreter.(Interpreter.stack) value in
  interpreter <| Interpreter.stack := stack |>
  )))).

Lemma good_size
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{IInterpreterTypes : !InterpreterTypes.C WIRE_types}
    mem
    (offset : usize) :
  List.length
    (IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.Deref_for_Synthetic)
    .(Deref.deref).(RefStub.projection)
    (IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.slice_len) mem
      offset 32)) =
  32%nat.
Admitted.

Lemma mload_eq
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
      (run_mload run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        mload interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  unfold mload.
  gas_macro_eq idtac.
  popn_top_macro_eq InterpreterTypesEq.
  as_usize_or_fail_macro_eq InterpreterTypesEq.
  resize_memory_macro_eq InterpreterTypesEq.
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    s_apply Impl_Uint.try_from_be_slice_eq.
  }
  s. {
    apply Impl_Option.unwrap_eq.
    set (mem := snd _).
    set (slice := _.(MemoryTrait.Deref_for_Synthetic).(Deref.deref).(RefStub.projection) _).
    assert (H_size : List.length slice = 32%nat) by apply good_size.
    unfold Impl_Uint.try_from_be_slice.
    rewrite H_size; cbn.
    reflexivity.
  }
  s.
  now destruct _.(MemoryTrait.resize).
Qed.
