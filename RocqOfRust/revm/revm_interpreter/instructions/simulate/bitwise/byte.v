Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.links.cmp.
Require Import core.num.simulate.mod.
Require Import core.simulate.cmp.
Require Import core.simulate.result.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.bitwise.byte.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.links.lib.
Require Import ruint.simulate.bits.
Require Import ruint.simulate.cmp.
Require Import ruint.simulate.from.
Require Import ruint.simulate.lib.

Definition op_byte
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  popn_top_macro interpreter 1 id (fun arr top interpreter =>
  let '⟬ op1 ⟭ := arr.(array.value) in
  let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
  let o1 := as_usize_saturated_macro op1 in
  let result :=
    if i[o1] <? 32
    then
      (* `31 - o1` because `byte` returns LE, while we want BE *)
      {| Uint.value := i[Impl_Uint.byte op2 ((31 - i[o1]) mod 2^64)] |}
    else
      {| Uint.value := 0 |} in
  let stack :=
    top.(RefStub.injection)
      interpreter.(Interpreter.stack) result in
  interpreter
    <| Interpreter.stack := stack |>
  )).

Lemma op_byte_eq
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
      (run_byte run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        op_byte interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  unfold op_byte.
  gas_macro_eq InterpreterTypesEq.
  popn_top_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t aliases.U256.t _ |- _ => destruct array as [[op1 []]]; cbn
  end.
  eapply Run.Let with (result := (Output.Success (as_usize_saturated_macro op1), _)). {
    as_usize_saturated_macro_eq.
  }
  s.
  destruct (_ <? 32) eqn:H_lt_eq.
  { s. { apply Impl_Uint.byte_eq; repeat unshelve econstructor. }
    s. { apply Impl_Uint.from_eq; [typeclasses eauto | easy]. }
    s.
  }
  { s. { apply Impl_Uint.ZERO_eq. }
    s.
  }
Qed.
