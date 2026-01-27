Require Import simulate.RocqOfRust.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.lt.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import ruint.links.lib.

(** Test that LT correctly computes 25 < 23 = false, resulting in 0 on stack *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 25 |};
    {| Uint.value := 23 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_lt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that LT correctly computes 10 < 20 = true, resulting in 1 on stack *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 10 |};
    {| Uint.value := 20 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_lt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 1 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that LT correctly computes 5 < 5 = false, resulting in 0 on stack *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 5 |};
    {| Uint.value := 5 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_lt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.
