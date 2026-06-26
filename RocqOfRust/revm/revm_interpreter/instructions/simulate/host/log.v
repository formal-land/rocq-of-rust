Require Import simulate.RocqOfRust.
Require Import alloc.links.alloc.
Require Import core.links.array.
Require Import alloc.links.raw_vec.
Require Import alloc.vec.links.mod.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.log.links.mod.
Require Import core.ops.simulate.deref.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.instructions.links.host.log.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.

Definition topics_from_array
    (N : usize)
    (topics : array.t aliases.U256.t N) :
    Vec.t aliases.U256.t Global.t :=
  {|
    Vec.buf := {| RawVec.value := ArrayPairs.to_list topics.(array.value) |};
    Vec.len := N;
  |}.

Definition finish_log
    (N : usize)
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H)
    (data : alloy_primitives.bytes.links.mod.Bytes.t) :
    Interpreter.t WIRE WIRE_types * H :=
  popn_macro interpreter N
    (fun interpreter => (interpreter, host)) (fun topics interpreter =>
  let target :=
    IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.target_address)
      interpreter.(Interpreter.input) in
  let topics := topics_from_array N topics in
  let log' : Log.t LogData.t := {|
    Log.address := target;
    Log.data := {|
      LogData.topics := topics;
      LogData.data := data;
    |};
  |} in
  let host := IHost.(Host.log) host log' in
  (interpreter, host)
  ).

Definition log
    (N : usize)
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  require_non_staticcall_macro interpreter
    (fun interpreter => (interpreter, host)) (fun interpreter =>
  popn_macro interpreter 2 (fun interpreter => (interpreter, host)) (fun arr interpreter =>
    let '⟬ offset; len ⟭ := arr.(array.value) in
    as_usize_or_fail_macro interpreter len None
      (fun interpreter => (interpreter, host)) (fun len interpreter =>
    gas_or_fail_macro interpreter
      (calc.log_cost (M.cast_integer IntegerKind.U8 N) (M.cast_integer IntegerKind.U64 len))
      (fun interpreter => (interpreter, host)) (fun interpreter =>
    if i[len] =? 0 then
      finish_log N interpreter host Impl_Bytes.new
    else
      as_usize_or_fail_macro interpreter offset None
        (fun interpreter => (interpreter, host)) (fun offset interpreter =>
      resize_memory_macro interpreter offset len
        (fun interpreter => (interpreter, host)) (fun interpreter =>
        let slice :=
          IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.slice_len)
            interpreter.(Interpreter.memory)
            offset
            len in
        let data :=
          IInterpreterTypes
            .(InterpreterTypes.MemoryTrait_for_Memory)
            .(MemoryTrait.Deref_for_Synthetic)
            .(Deref.deref)
            .(RefStub.projection)
            slice in
        finish_log N interpreter host (Impl_Bytes.copy_from_slice data))
  ))))).

Lemma log_eq
    (N : usize)
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_Host_for_H : Host.Run H H_types)
    `{IInterpreterTypes : !InterpreterTypes.C WIRE_types}
    `{InterpreterTypesEq :
      !InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes}
    `{IHost : !Host.C H H_types}
    `{HostEq : !Host.Eq.t IHost}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref (A := H) 1 in
  let context := {|
    instruction_context.InstructionContext.interpreter := ref_interpreter;
    instruction_context.InstructionContext.host := ref_host;
  |} in
  let result := log N interpreter host in
  {{
    SimulateM.eval_f
      (run_log (N := N) run_InterpreterTypes_for_WIRE run_Host_for_H context)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
Admitted.
