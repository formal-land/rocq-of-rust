Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.ops.simulate.range.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.interpreter_action.simulate.call_inputs.
Require Import revm.revm_interpreter.instructions.simulate.system.memory_resize.
Require Import revm.revm_interpreter.instructions.links.system.calldatacopy.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.

Definition calldatacopy
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  popn_macro interpreter 3 id (fun arr interpreter =>
  let '⟬ memory_offset; data_offset; len ⟭ := arr.(array.value) in
  as_usize_or_fail_macro interpreter len None id (fun len interpreter =>
  let '(memory_offset_opt, interpreter) := memory_resize interpreter memory_offset len in
  match memory_offset_opt with
  | None => interpreter
  | Some memory_offset =>

  let data_offset := as_usize_saturated_macro data_offset in
  let input :=
    IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.input)
      .(RefStub.projection) interpreter.(Interpreter.input) in
  let memory :=
    match input with
    | call_inputs.CallInput.Bytes bytes =>
      IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.set_data)
        interpreter.(Interpreter.memory)
        memory_offset
        data_offset
        len
        (call_inputs.CallInput.bytes_as_ref bytes)
    | call_inputs.CallInput.SharedBuffer range =>
      IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.set_data_from_global)
        interpreter.(Interpreter.memory)
        memory_offset
        data_offset
        len
        range
    end in
  interpreter <| Interpreter.memory := memory |>
  end)).

Lemma calldatacopy_eq
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
        (run_calldatacopy run_InterpreterTypes_for_WIRE context)
        [interpreter; host]%stack 🌲
      (
        Output.Success tt,
        [calldatacopy interpreter; host]%stack
      )
    }}.
Proof.
Opaque memory_resize.
  with_strategy transparent [run_calldatacopy] unfold calldatacopy, run_calldatacopy; cbn.
  popn_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t aliases.U256.t _ |- _ =>
    destruct array as [[memory_offset [data_offset [len []]]]]
  end.
  as_usize_or_fail_macro_eq InterpreterTypesEq.
  s. {
    apply memory_resize_eq.
  }
  rename interpreter into initial_interpreter.
  destruct memory_resize as [[?memory_offset|] ?interpreter]; cbn. 2: {
    s.
  }
  eapply Run.Let with (result := (Output.Success (as_usize_saturated_macro data_offset), _)). {
    as_usize_saturated_macro_eq.
  }
  s. {
    apply InterpreterTypesEq.
  }
  destruct
    (IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.input)
      .(RefStub.projection) interpreter.(Interpreter.input)) as [range | bytes]
      eqn:H_input; cbn.
  - r.
    rewrite H_input; cbn.
    r.
    rewrite H_input; cbn.
    r.
    s. {
      apply Impl_Clone_for_Range.clone_eq.
      unshelve eapply CanRead.Mutable.
      - cbn; repeat constructor.
      - cbn; rewrite H_input; reflexivity.
    }
    cbn.
    eapply Run.Call. {
      s_apply InterpreterTypesEq.
    }
    cbn; s.
  - r.
    rewrite H_input; cbn.
    r.
    s. {
      apply alloy_primitives.bytes.simulate.mod.Impl_AsRef_slice_u8_for_Bytes.as_ref_eq
        with (self := bytes).
      unshelve eapply CanRead.Mutable.
      - cbn; repeat constructor.
      - cbn; rewrite H_input; reflexivity.
    }
    cbn.
    eapply Run.Call. {
      s_apply InterpreterTypesEq.
      cbn; rewrite H_input; reflexivity.
    }
    cbn; s.
Qed.
