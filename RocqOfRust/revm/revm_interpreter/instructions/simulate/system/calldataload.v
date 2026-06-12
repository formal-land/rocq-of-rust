Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import core.convert.simulate.mod.
Require Import core.simulate.cmp.
Require Import core.slice.simulate.mod.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.system.calldataload.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.links.lib.

Definition calldataload
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  popn_top_macro interpreter 0
    id (fun _ offset_ptr_stub interpreter =>
  let offset_ptr := offset_ptr_stub.(RefStub.projection) interpreter.(Interpreter.stack) in
  let offset := as_usize_saturated_macro offset_ptr in
  let input :=
    IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.input)
      .(RefStub.projection) interpreter.(Interpreter.input) in
  let input_len := Impl_Slice.len input in
  let word :=
    if i[offset] <? i[input_len] then
      let count := Z.min 32 i[input_len -i offset] in
      Impl_FixedBytes.ZERO
    else
      Impl_FixedBytes.ZERO in
  let stack :=
    offset_ptr_stub.(RefStub.injection)
      interpreter.(Interpreter.stack)
      (Into.into word) in
  interpreter <| Interpreter.stack := stack |>
  )).

Lemma calldataload_eq
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
        (run_calldataload run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
        [interpreter; host]%stack 🌲
      (
        Output.Success tt,
        [calldataload interpreter; host]%stack
      )
    }}.
Proof.
Admitted.
