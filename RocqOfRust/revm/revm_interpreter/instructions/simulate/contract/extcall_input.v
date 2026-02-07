Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import core.links.array.
Require Import core.ops.simulate.deref.
Require Import core.ops.simulate.range.
Require Import core.simulate.option.
Require Import revm.revm_interpreter.instructions.contract.simulate.call_helpers.
Require Import revm.revm_interpreter.instructions.links.contract.extcall_input.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.

Definition extcall_input
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    option Bytes.t * Interpreter.t WIRE WIRE_types :=
  popn_macro interpreter 2
    (fun interpreter => (None, interpreter)) (fun arr interpreter =>
  let '⟬ input_offset; input_size ⟭ := arr.(array.value) in
  let '(return_memory_offset_opt, interpreter) :=
    call_helpers.resize_memory interpreter input_offset input_size in
  match return_memory_offset_opt with
  | None => (None, interpreter)
  | Some return_memory_offset =>
    if Impl_Range.is_empty return_memory_offset then
      (Some Impl_Bytes.new, interpreter)
    else
      let slice :=
        IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.slice)
          interpreter.(Interpreter.memory) return_memory_offset in
      let slice : list u8 :=
        IInterpreterTypes
          .(InterpreterTypes.MemoryTrait_for_Memory)
          .(MemoryTrait.Deref_for_Synthetic)
          .(Deref.deref)
          .(RefStub.projection)
          slice in
      (Some (Impl_Bytes.copy_from_slice slice), interpreter)
  end).

Lemma extcall_input_eq
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    `{IInterpreterTypes : !InterpreterTypes.C WIRE_types}
    `{InterpreterTypesEq :
      !InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (stack : Stack.t) :
  let ref_interpreter := make_ref 0 in
  {{
    SimulateM.eval_f
      (run_extcall_input run_InterpreterTypes_for_WIRE ref_interpreter)
      (interpreter :: stack)%stack 🌲
    let result := extcall_input interpreter in
    (
      Output.Success (fst result),
      (snd result :: stack)%stack
    )
  }}.
Proof.
  apply Run.remove_extra_stack1.
  with_strategy transparent [run_extcall_input]
    unfold run_extcall_input, extcall_input; cbn.
  popn_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t _ _ |- _ =>
    destruct array as [[input_offset [input_size []]]]
  end.
  s. {
    apply call_helpers.resize_memory_eq; typeclasses eauto.
  }
  destruct call_helpers.resize_memory as [[return_memory_offset|] ?interpreter]; cbn. 2: {
    s. {
      s_apply Impl_Try_for_Option.Eq.I.
    }
    s. {
      s_apply Impl_FromResidual_Infallible_for_Option.Eq.I.
    }
    s.
  }
  s. {
    s_apply Impl_Try_for_Option.Eq.I.
  }
  s. {
    s_apply Impl_Range.is_empty_eq.
  }
  s.
  destruct Impl_Range.is_empty; cbn.
  { s. {
      apply Impl_Bytes.new_eq.
    }
    s.
  }
  { s. {
      s_apply @Impl_Clone_for_Range.Eq.I.
    }
    s. {
      apply InterpreterTypesEq.
    }
    s. {
      apply InterpreterTypesEq.
    }
    s. {
      s_apply @Impl_Bytes.copy_from_slice_eq.
    }
    s.
  }
Qed.
