Require Import simulate.RocqOfRust.
Require Import revm.revm_interpreter.instructions.simulate.system.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
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
