Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.utils.simulate.mod.
Require Import core.convert.links.mod.
Require Import core.convert.simulate.mod.
Require Import core.links.array.
Require Import core.ops.simulate.deref.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.instructions.links.system.keccak256.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.simulate.lib.
Require Import ruint.links.lib.

Definition keccak256
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  popn_top_macro interpreter 1
    id (fun arr top_stub interpreter =>
  let '⟬ offset ⟭ := arr.(array.value) in
  let top := top_stub.(RefStub.projection) interpreter.(Interpreter.stack) in
  as_usize_or_fail_macro interpreter top None
    id (fun len interpreter =>
  gas_or_fail_macro interpreter (keccak256_cost len)
    id (fun interpreter =>
  if i[len] =? 0 then
    let hash := KECCAK_EMPTY in
    let stack :=
      top_stub.(RefStub.injection)
        interpreter.(Interpreter.stack)
        (Into.into hash) in
    interpreter <| Interpreter.stack := stack |>
  else
    as_usize_or_fail_macro interpreter offset None
      id (fun from interpreter =>
    resize_memory_macro interpreter from len
      id (fun interpreter =>
    let slice :=
      IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.slice_len)
        interpreter.(Interpreter.memory) from len in
    let slice : list u8 := Deref.deref.(RefStub.projection) slice in
    let hash := keccak256 (Ref.immediate _ slice) in
    let stack :=
      top_stub.(RefStub.injection)
        interpreter.(Interpreter.stack)
        (Into.into hash) in
    interpreter <| Interpreter.stack := stack |>
  ))))).

Lemma keccak256_eq
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
    {{
      SimulateM.eval_f
        (run_keccak256 run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
        [interpreter; host]%stack 🌲
      (
        Output.Success tt,
        [keccak256 interpreter; host]%stack
      )
    }}.
Proof.
Admitted.
