Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_interpreter.instructions.contract.simulate.call_helpers.
Require Import revm.revm_interpreter.instructions.simulate.contract.extcall_input.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import ruint.links.lib.

(** extcall_input: underflow path *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let '(input_opt, result_interpreter) := extcall_input interpreter in
  input_opt = None /\
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  split; reflexivity.
Qed.

(** extcall_input: zero-size input yields empty bytes *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};  (* input_offset *)
    {| Uint.value := 0 |}   (* input_size *)
  ] |} in
  let interpreter := make_interpreter stack in
  let '(input_opt, _) := extcall_input interpreter in
  input_opt = Some Impl_Bytes.new.
Proof.
Admitted.

(** get_memory_input_and_out_ranges: underflow path *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let '(io_opt, result_interpreter) := get_memory_input_and_out_ranges interpreter in
  io_opt = None /\
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  split; reflexivity.
Qed.

(** get_memory_input_and_out_ranges: zero ranges produce Some result *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};  (* in_offset *)
    {| Uint.value := 0 |};  (* in_len *)
    {| Uint.value := 0 |};  (* out_offset *)
    {| Uint.value := 0 |}   (* out_len *)
  ] |} in
  let interpreter := make_interpreter stack in
  let '(io_opt, _) := get_memory_input_and_out_ranges interpreter in
  match io_opt with
  | Some _ => True
  | None => False
  end.
Proof.
  timeout 1 vm_compute.
  exact I.
Qed.
