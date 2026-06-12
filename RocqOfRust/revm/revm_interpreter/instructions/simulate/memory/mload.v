Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.num.simulate.mod.
Require Import core.ops.simulate.deref.
Require Import core.simulate.option.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.memory.mload.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.interpreter.simulate.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_context.
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

Definition halt_memory_oog
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{IInterpreterTypes : !InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  let action :=
    interpreter_action.InterpreterAction.Return {|
      InterpreterResult.result := instruction_result.InstructionResult.MemoryOOG;
      InterpreterResult.output := Impl_Bytes.new;
      InterpreterResult.gas := interpreter.(Interpreter.gas);
    |} in
  let bytecode :=
    IInterpreterTypes
      .(InterpreterTypes.LoopControl_for_Bytecode)
      .(LoopControl.set_action)
      interpreter.(Interpreter.bytecode)
      action in
  interpreter <| Interpreter.bytecode := bytecode |>.

Lemma halt_memory_oog_eq
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (stack_rest : Stack.t) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  {{
    SimulateM.eval_f
      (Impl_Interpreter.run_halt_memory_oog WIRE ref_interpreter)
      (interpreter :: stack_rest)%stack 🌲
    (
      Output.Success tt,
      (halt_memory_oog interpreter :: stack_rest)%stack
    )
  }}.
Proof.
Admitted.

Definition mload
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{IInterpreterTypes : !InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  popn_top_macro interpreter 0 id (fun _ top_stub interpreter =>
  let top := top_stub.(RefStub.projection) interpreter.(Interpreter.stack) in
  as_usize_or_fail_macro interpreter top None id (fun offset interpreter =>
  let '(success, interpreter) := resize_memory interpreter offset 32 in
  if negb success then
    halt_memory_oog interpreter
  else
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
  )).

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
  let context : InstructionContext.t H WIRE WIRE_types :=
    @InstructionContext.Build_t H WIRE H1 H0 WIRE_types H2 ref_interpreter ref_host in
  {{
    SimulateM.eval_f
      (run_mload run_InterpreterTypes_for_WIRE context)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        mload interpreter;
        _host
      ]%stack
    )
  }}.
Admitted.
