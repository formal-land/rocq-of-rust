Require Import simulate.RocqOfRust.
Require Import revm.revm_interpreter.instructions.simulate.stack.dup.
Require Import revm.revm_interpreter.instructions.simulate.stack.pop.
Require Import revm.revm_interpreter.instructions.simulate.stack.push.
Require Import revm.revm_interpreter.instructions.simulate.stack.push0.
Require Import revm.revm_interpreter.instructions.simulate.stack.swap.
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

(** ** DUP tests *)

(** Test that DUP1 duplicates the top element: [a, b] -> [a, a, b] *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 42 |};
    {| Uint.value := 10 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := dup {| Integer.value := 1 |} interpreter in
  result.(Interpreter.stack).(Stack.value) = [
    {| Uint.value := 42 |};
    {| Uint.value := 42 |};
    {| Uint.value := 10 |}
  ].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that DUP2 duplicates the second element: [a, b, c] -> [b, a, b, c] *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 1 |};
    {| Uint.value := 2 |};
    {| Uint.value := 3 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := dup {| Integer.value := 2 |} interpreter in
  result.(Interpreter.stack).(Stack.value) = [
    {| Uint.value := 2 |};
    {| Uint.value := 1 |};
    {| Uint.value := 2 |};
    {| Uint.value := 3 |}
  ].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** SWAP tests *)

(** Test that SWAP1 swaps the top two elements: [a, b, c] -> [b, a, c] *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 1 |};
    {| Uint.value := 2 |};
    {| Uint.value := 3 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := swap {| Integer.value := 1 |} interpreter in
  result.(Interpreter.stack).(Stack.value) = [
    {| Uint.value := 2 |};
    {| Uint.value := 1 |};
    {| Uint.value := 3 |}
  ].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that SWAP2 swaps top and third element: [a, b, c, d] -> [c, b, a, d] *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 1 |};
    {| Uint.value := 2 |};
    {| Uint.value := 3 |};
    {| Uint.value := 4 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := swap {| Integer.value := 2 |} interpreter in
  result.(Interpreter.stack).(Stack.value) = [
    {| Uint.value := 3 |};
    {| Uint.value := 2 |};
    {| Uint.value := 1 |};
    {| Uint.value := 4 |}
  ].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** PUSH tests *)

(** Test that PUSH1 pushes a value onto the stack (zero bytes from test bytecode) *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let result := push 1 interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that PUSH1 does not set an error *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let result := push 1 interpreter in
  result.(Interpreter.control).(Control.instruction_result) = None.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.
