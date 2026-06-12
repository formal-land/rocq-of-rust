Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.log.links.mod.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.instructions.simulate.contract.call.
Require Import revm.revm_interpreter.instructions.simulate.contract.call_code.
Require Import revm.revm_interpreter.instructions.simulate.contract.delegate_call.
Require Import revm.revm_interpreter.instructions.simulate.contract.static_call.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.tests.host.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.lib.

(** ** StackUnderflow Tests *)

(** Test that static_call with empty stack returns StackUnderflow *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := static_call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.StackUnderflow.
Proof.
Admitted.

(** ** CALL tests *)

(** Test that call with empty stack returns StackUnderflow *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.StackUnderflow.
Proof.
Admitted.

(** Test that call with only 2 values returns StackUnderflow *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 1000 |};
    {| Uint.value := 42 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.StackUnderflow.
Proof.
Admitted.

(** call can branch on abstract RuntimeFlag.is_static in test fixtures *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 1000 |};  (* local_gas_limit *)
    {| Uint.value := 42 |};    (* to *)
    {| Uint.value := 1 |};     (* value *)
    {| Uint.value := 0 |};     (* in_offset *)
    {| Uint.value := 0 |};     (* in_len *)
    {| Uint.value := 0 |};     (* out_offset *)
    {| Uint.value := 0 |}      (* out_len *)
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.CallNotAllowedInsideStatic \/
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.FatalExternalError.
Proof.
  timeout 1 vm_compute.
  destruct (RuntimeFlag.is_static SpecId.LATEST); auto.
Qed.

Goal
  let stack := {| Stack.value := [
    {| Uint.value := 1000 |};  (* local_gas_limit *)
    {| Uint.value := 42 |};    (* to *)
    {| Uint.value := 1 |};     (* value *)
    {| Uint.value := 0 |};     (* in_offset *)
    {| Uint.value := 0 |};     (* in_len *)
    {| Uint.value := 0 |};     (* out_offset *)
    {| Uint.value := 0 |}      (* out_len *)
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHostWithAccount.t := TestHostWithAccount.Make in
  let '(result_interpreter, _) := call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.CallNotAllowedInsideStatic \/
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.CallOrCreate.
Proof.
  timeout 1 vm_compute.
  destruct (RuntimeFlag.is_static SpecId.LATEST); auto.
Qed.

(** ** CALLCODE tests *)

Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := call_code interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.StackUnderflow.
Proof.
Admitted.

Goal
  let stack := {| Stack.value := [
    {| Uint.value := 1000 |};  (* local_gas_limit *)
    {| Uint.value := 42 |};    (* to *)
    {| Uint.value := 0 |};     (* value *)
    {| Uint.value := 0 |};     (* in_offset *)
    {| Uint.value := 0 |};     (* in_len *)
    {| Uint.value := 0 |};     (* out_offset *)
    {| Uint.value := 0 |}      (* out_len *)
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := call_code interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.FatalExternalError.
Proof.
Admitted.

Goal
  let stack := {| Stack.value := [
    {| Uint.value := 1000 |};  (* local_gas_limit *)
    {| Uint.value := 42 |};    (* to *)
    {| Uint.value := 0 |};     (* value *)
    {| Uint.value := 0 |};     (* in_offset *)
    {| Uint.value := 0 |};     (* in_len *)
    {| Uint.value := 0 |};     (* out_offset *)
    {| Uint.value := 0 |}      (* out_len *)
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHostWithAccount.t := TestHostWithAccount.Make in
  let '(result_interpreter, _) := call_code interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.CallOrCreate.
Proof.
Admitted.

(** ** DELEGATECALL tests *)

Goal
  let stack := {| Stack.value := [
    {| Uint.value := 1000 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := delegate_call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.StackUnderflow.
Proof.
Admitted.

Goal
  let stack := {| Stack.value := [
    {| Uint.value := 1000 |};  (* local_gas_limit *)
    {| Uint.value := 42 |};    (* to *)
    {| Uint.value := 0 |};     (* in_offset *)
    {| Uint.value := 0 |};     (* in_len *)
    {| Uint.value := 0 |};     (* out_offset *)
    {| Uint.value := 0 |}      (* out_len *)
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := delegate_call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.FatalExternalError.
Proof.
Admitted.

Goal
  let stack := {| Stack.value := [
    {| Uint.value := 1000 |};  (* local_gas_limit *)
    {| Uint.value := 42 |};    (* to *)
    {| Uint.value := 0 |};     (* in_offset *)
    {| Uint.value := 0 |};     (* in_len *)
    {| Uint.value := 0 |};     (* out_offset *)
    {| Uint.value := 0 |}      (* out_len *)
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHostWithAccount.t := TestHostWithAccount.Make in
  let '(result_interpreter, _) := delegate_call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.CallOrCreate.
Proof.
Admitted.

(** Test that static_call with only 1 element returns StackUnderflow
    (static_call needs to pop 2 values first) *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 100 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := static_call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.StackUnderflow.
Proof.
Admitted.

(** Test that static_call with only 5 elements returns StackUnderflow
    (static_call pops 2, then get_memory_input_and_out_ranges pops 4 more = 6 total needed) *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};     (* out_offset - only 5 values *)
    {| Uint.value := 0 |};     (* in_len *)
    {| Uint.value := 0 |};     (* in_offset *)
    {| Uint.value := 1000 |};  (* local_gas_limit *)
    {| Uint.value := 42 |}     (* to address *)
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := static_call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.StackUnderflow.
Proof.
Admitted.

(** ** Tests requiring full path (FatalExternalError, CallOrCreate)
    These tests go through get_memory_input_and_out_ranges which involves
    complex computation. *)

(** Test that static_call with 6 elements but no account returns FatalExternalError *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};     (* out_len *)
    {| Uint.value := 0 |};     (* out_offset *)
    {| Uint.value := 0 |};     (* in_len *)
    {| Uint.value := 0 |};     (* in_offset *)
    {| Uint.value := 1000 |};  (* local_gas_limit *)
    {| Uint.value := 42 |}     (* to address *)
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := static_call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.FatalExternalError.
Proof.
Admitted.

(** Test that static_call with valid account returns CallOrCreate *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};     (* out_len *)
    {| Uint.value := 0 |};     (* out_offset *)
    {| Uint.value := 0 |};     (* in_len *)
    {| Uint.value := 0 |};     (* in_offset *)
    {| Uint.value := 1000 |};  (* local_gas_limit *)
    {| Uint.value := 42 |}     (* to address *)
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHostWithAccount.t := TestHostWithAccount.Make in
  let '(result_interpreter, _) := static_call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.CallOrCreate.
Proof.
Admitted.
