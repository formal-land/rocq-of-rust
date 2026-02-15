Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import core.convert.simulate.mod.
Require Import revm.revm_interpreter.instructions.simulate.system.gas.
Require Import revm.revm_interpreter.instructions.simulate.system.keccak256.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_primitives.simulate.lib.
Require Import ruint.links.lib.

(** ** GAS tests *)

(** Test that GAS pushes remaining gas after BASE cost deduction.
    Gas starts at 1000000, BASE cost = 2. After deducting 2, remaining = 999998. *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let result := gas interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 999998 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** KECCAK256 tests *)

(** Test that KECCAK256 with len=0 pushes the hash of the empty input.
    Stack: [offset=0, len=0] -> top = Into.into KECCAK_EMPTY *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 0 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := keccak256 interpreter in
  result.(Interpreter.stack).(Stack.value) =
    [Into.into KECCAK_EMPTY].
Proof.
  timeout 5 vm_compute.
  reflexivity.
Qed.
