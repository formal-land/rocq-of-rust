Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.links.cmp.
Require Import core.ops.simulate.bit.
Require Import core.simulate.cmp.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.bitwise.shr.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import revm.revm_specification.simulate.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.bits.
Require Import ruint.simulate.cmp.
Require Import ruint.simulate.from.

(* Helper to saturate usize conversion *)
Definition as_usize_saturated (x : aliases.U256.t) : usize :=
  if x.(Uint.value) >=? Z.of_nat (Nat.pow 2 64)
  then {| Integer.value := Z.of_nat (Nat.pow 2 64 - 1) |}
  else {| Integer.value := x.(Uint.value) |}.

Definition op_shr
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  check_macro interpreter SpecId.CONSTANTINOPLE id (fun interpreter =>
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  popn_top_macro interpreter {| Integer.value := 1 |} id (fun arr top interpreter =>
    let '{| ArrayPair.x := shift_op |} := arr.(array.value) in
    let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
    let shift := as_usize_saturated shift_op in
    let result :=
      if shift.(Integer.value) <? 256
      then Impl_Shr_for_Uint.shr op2 shift
      else {| Uint.value := 0 |} in
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack) result in
    interpreter
      <| Interpreter.stack := stack |>
  ))).

Lemma op_shr_eq
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
      (run_bitwise_shr run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        op_shr interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  unfold op_shr.
Admitted.
(* check_macro_eq InterpreterTypesEq.
gas_macro_eq InterpreterTypesEq.
popn_top_macro_eq InterpreterTypesEq.
cbn.
get_can_access.
eapply Run.Call. {
apply Shr.Eq.shr.
}
cbn.
get_can_access.
cbn.
apply Run.PureEq; repeat f_equal.
Qed. *)
