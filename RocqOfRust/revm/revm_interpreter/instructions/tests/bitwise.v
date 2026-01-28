Require Import links.RocqOfRust.
Require Import RocqOfRust.simulate.M.
Require Import RocqOfRust.lib.simulate.lib.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.lt.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import ruint.links.lib.

Goal
  let stack := {| Stack.value := [
    {| Uint.value := 25 |};
    {| Uint.value := 23 |}
  ] |} in
  let interpreter := make_interpreter stack in
  macros.gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  macros.popn_top_macro interpreter {| Integer.value := 1 |} id (fun arr top interpreter =>
  interpreter)) =
  op_lt interpreter.
Proof.
  intros.
  unfold lt.
  unfold macros.gas_macro.
  unfold constants.VERYLOW.
  unfold gas.Impl_Gas.record_cost.
  timeout 1 cbn.
  timeout 1 cbv.
Abort.
