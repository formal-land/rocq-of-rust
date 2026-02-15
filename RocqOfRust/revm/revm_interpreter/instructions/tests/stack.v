Require Import simulate.RocqOfRust.
Require Import revm.revm_interpreter.instructions.simulate.stack.pop.
Require Import revm.revm_interpreter.instructions.simulate.stack.push0.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import ruint.links.lib.

(** ** POP tests *)

(** Test that POP removes the top element from the stack *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 42 |};
    {| Uint.value := 10 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := pop interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 10 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that POP on empty stack returns StackUnderflow *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let result := pop interpreter in
  result.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** PUSH0 tests *)

(** Test that PUSH0 pushes 0 onto the stack *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let result := push0 interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.
