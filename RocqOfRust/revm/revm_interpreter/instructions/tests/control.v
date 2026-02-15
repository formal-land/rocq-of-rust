Require Import simulate.RocqOfRust.
Require Import revm.revm_interpreter.instructions.simulate.control.stop.
Require Import revm.revm_interpreter.instructions.simulate.control.invalid.
Require Import revm.revm_interpreter.instructions.simulate.control.unknown.
Require Import revm.revm_interpreter.instructions.simulate.control.ret.
Require Import revm.revm_interpreter.instructions.simulate.control.revert.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
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

(** ** UNKNOWN tests *)

(** Test that UNKNOWN sets instruction_result to OpcodeNotFound *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let result := unknown interpreter in
  result.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.OpcodeNotFound.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** RET tests *)

(** Test that RET with offset=0, len=0 sets instruction_result to Return *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 0 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := ret interpreter in
  result.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.Return.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that RET with offset=0, len=0 sets next_action to Return *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 0 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := ret interpreter in
  match result.(Interpreter.control).(Control.next_action) with
  | Some (InterpreterAction.Return _) => True
  | _ => False
  end.
Proof.
  timeout 1 vm_compute.
  exact I.
Qed.

(** ** REVERT tests *)

(** Test that REVERT with offset=0, len=0 sets instruction_result to Revert *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 0 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := revert interpreter in
  result.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.Revert.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.
