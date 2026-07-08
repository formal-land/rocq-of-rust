Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import bytes.simulate.bytes.
Require Import core.links.array.
Require Import core.slice.simulate.mod.
Require Import core.num.simulate.mod.
Require Import revm.revm_interpreter.instructions.simulate.system.memory_resize.
Require Import revm.revm_interpreter.instructions.links.system.returndatacopy.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter.
Require Import revm.revm_interpreter.simulate.interpreter_types.

Definition returndatacopy
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  check_macro interpreter SpecId.BYZANTIUM id (fun interpreter =>
  popn_macro interpreter 3
    id (fun arr interpreter =>
  let '⟬ memory_offset; offset; len ⟭ := arr.(array.value) in

  as_usize_or_fail_macro interpreter len None id (fun len interpreter =>
  let data_offset := as_usize_saturated_macro offset in

  let data_end := Impl_usize.saturating_add data_offset len in
  let return_data :=
    IInterpreterTypes.(InterpreterTypes.ReturnData_for_ReturnData).(ReturnData.buffer)
      .(RefStub.projection) interpreter.(Interpreter.return_data) in
  let return_data := return_data.(Bytes.value) in
  let return_data_len := Impl_Bytes.len return_data in
  if i[data_end] >? i[return_data_len] then
    halt interpreter instruction_result.InstructionResult.OutOfOffset
  else
    let '(memory_offset_opt, interpreter) := memory_resize interpreter memory_offset len in
    match memory_offset_opt with
    | None => interpreter
    | Some memory_offset =>
      let return_data :=
        IInterpreterTypes.(InterpreterTypes.ReturnData_for_ReturnData).(ReturnData.buffer)
          .(RefStub.projection) interpreter.(Interpreter.return_data) in
      let return_data := return_data.(Bytes.value).(bytes.Bytes.value) in
      let memory :=
        IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.set_data)
          interpreter.(Interpreter.memory)
          memory_offset
          data_offset
          len
          return_data in
      interpreter <| Interpreter.memory := memory |>
    end
  ))).

Lemma returndatacopy_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref (A := H) 1 in
  let context := {|
    instruction_context.InstructionContext.interpreter := ref_interpreter;
    instruction_context.InstructionContext.host := ref_host;
  |} in
    {{
      SimulateM.eval_f
        (run_returndatacopy run_InterpreterTypes_for_WIRE context)
        [interpreter; host]%stack 🌲
      (
        Output.Success tt,
        [returndatacopy interpreter; host]%stack
      )
    }}.
Proof.
Opaque memory_resize.
  with_strategy transparent [run_returndatacopy] unfold returndatacopy, run_returndatacopy; cbn.
  check_macro_eq InterpreterTypesEq.
  popn_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t aliases.U256.t _ |- _ =>
    destruct array as [[memory_offset [offset [len []]]]]
  end.
  as_usize_or_fail_macro_eq InterpreterTypesEq.
  eapply Run.Let with (result := (Output.Success (as_usize_saturated_macro offset), _)). {
    as_usize_saturated_macro_eq.
  }
  s. {
    apply Impl_usize.saturating_add_eq.
  }
  (* We explore all the combinations for the `if` *)
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply alloy_primitives.bytes.simulate.mod.Impl_Deref_for_Bytes.Eq.I.
  }
  s. {
    pose proof bytes.simulate.bytes.Impl_Bytes.len_eq as H_apply.
    s_apply H_apply.
  }
  s.
  destruct (_ >? _) eqn:H_lt_eq; cbn.
  { s. {
      eapply halt_eq;
        try exact InterpreterTypesEq.
    }
    s.
  }
  { s. {
      apply memory_resize_eq.
    }
    destruct memory_resize as [[?memory_offset|] ?interpreter]; cbn; [|s].
    s. {
      apply InterpreterTypesEq.
    }
    s. {
      apply alloy_primitives.bytes.simulate.mod.Impl_Deref_for_Bytes.Eq.I.
    }
    s. {
      apply bytes.simulate.bytes.Impl_Deref_for_Bytes.Eq.I.
    }
    s. {
      s_apply InterpreterTypesEq.
    }
    s.
  }
Qed.
