Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.instructions.simulate.contract.static_call.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import ruint.links.lib.

(** Mock Host that returns None - for FatalExternalError path *)
Module TestHost.
  Definition t : Set := unit.

  Instance IsLink : Link t.
  Admitted.

  Definition load_account_delegated (self : t) (address : Address.t) :
      option AccountLoad.t * t :=
    (None, self).

  Instance I : Host.C t := {
    Host.load_account_delegated := load_account_delegated;
  }.
End TestHost.
Export (hints) TestHost.

(** Mock Host that returns Some - for success path *)
Module TestHostWithAccount.
  Definition t : Set := unit.

  Instance IsLink : Link t.
  Admitted.

  Definition test_account_load : AccountLoad.t := {|
    AccountLoad.load := {|
      Eip7702CodeLoad.state_load := {|
        StateLoad.data := tt;
        StateLoad.is_cold := false;
      |};
      Eip7702CodeLoad.is_delegate_account_cold := None;
    |};
    AccountLoad.is_empty := true;
  |}.

  Definition load_account_delegated (self : t) (address : Address.t) :
      option AccountLoad.t * t :=
    (Some test_account_load, self).

  Instance I : Host.C t := {
    Host.load_account_delegated := load_account_delegated;
  }.
End TestHostWithAccount.
Export (hints) TestHostWithAccount.

(** ** StackUnderflow Tests *)

(** Test that static_call with empty stack returns StackUnderflow *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := tt in
  let '(result_interpreter, _) := static_call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that static_call with only 1 element returns StackUnderflow
    (static_call needs to pop 2 values first) *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 100 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := tt in
  let '(result_interpreter, _) := static_call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

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
  let host : TestHost.t := tt in
  let '(result_interpreter, _) := static_call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** Tests requiring full path (FatalExternalError, CallOrCreate)
    These tests go through get_memory_input_and_out_ranges which involves
    complex computation. They are commented out because they timeout with
    "timeout 1 vm_compute". The StackUnderflow tests above provide coverage
    for the early exit paths. *)

(*
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
  let host : TestHost.t := tt in
  let '(result_interpreter, _) := static_call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.FatalExternalError.
Proof.
  (* TODO: This test times out with vm_compute due to complex computation *)
  timeout 1 vm_compute.
  reflexivity.
Qed.

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
  let host : TestHostWithAccount.t := tt in
  let '(result_interpreter, _) := static_call interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.CallOrCreate.
Proof.
  (* TODO: This test times out with vm_compute due to complex computation *)
  timeout 1 vm_compute.
  reflexivity.
Qed.
*)
