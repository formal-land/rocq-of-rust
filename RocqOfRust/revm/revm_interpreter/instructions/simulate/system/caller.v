Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.simulate.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import core.convert.simulate.mod.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.system.caller.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.instructions.simulate.utility.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.links.from.

Definition caller
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.BASE id (fun interpreter =>
  let caller :=
    IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.caller_address)
      interpreter.(Interpreter.input) in
  let value := Impl_IntoU256_for_Address.into_u256 caller in
  push_macro interpreter value
    id
    id
  ).

Lemma caller_eq
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
      (run_caller run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [caller interpreter; host]%stack
    )
  }}.
Proof.
Admitted.
