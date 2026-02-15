Require Import simulate.RocqOfRust.
Require Import revm.revm_interpreter.instructions.simulate.control.stop.
Require Import revm.revm_interpreter.instructions.simulate.control.invalid.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import ruint.links.lib.

(** ** STOP tests *)

(** Test that STOP sets instruction_result to Stop *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let result := stop interpreter in
  result.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.Stop.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** INVALID tests *)

(** Test that INVALID sets instruction_result to InvalidFEOpcode *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let result := invalid interpreter in
  result.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.InvalidFEOpcode.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.
