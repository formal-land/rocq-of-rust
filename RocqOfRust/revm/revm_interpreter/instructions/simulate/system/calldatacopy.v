Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
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
Admitted.
