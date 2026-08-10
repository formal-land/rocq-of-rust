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
Require Import revm.revm_interpreter.instructions.simulate.contract.create.
Require Import revm.revm_interpreter.instructions.simulate.contract.delegate_call.
Require Import revm.revm_interpreter.instructions.simulate.contract.static_call.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.interpreter_InterpreterResult.
Require Import revm.revm_interpreter.tests.host.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.lib.

Definition bytecode_action
    (interpreter : Interpreter.t WIRE WIRE_types) :
    option InterpreterAction.t :=
  interpreter.(Interpreter.bytecode).(Bytecode.action).

Definition bytecode_result
    (interpreter : Interpreter.t WIRE WIRE_types) :
    option InstructionResult.t :=
  match bytecode_action interpreter with
  | Some (InterpreterAction.Return result) =>
    Some result.(InterpreterResult.result)
  | _ => None
  end.

Definition is_call_frame
    (interpreter : Interpreter.t WIRE WIRE_types) : Prop :=
  match bytecode_action interpreter with
  | Some (InterpreterAction.NewFrame (FrameInput.Call _)) => True
  | _ => False
  end.

Definition is_create_frame
    (interpreter : Interpreter.t WIRE WIRE_types) : Prop :=
  match bytecode_action interpreter with
  | Some (InterpreterAction.NewFrame (FrameInput.Create _)) => True
  | _ => False
  end.

(** ** StackUnderflow Tests *)

(** Test that static_call with empty stack returns StackUnderflow *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := static_call interpreter host in
  bytecode_result result_interpreter = Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** CALL tests *)

(** Test that call with empty stack returns StackUnderflow *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := call interpreter host in
  bytecode_result result_interpreter = Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that call with only 2 values returns StackUnderflow *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 1000 |};
    {| Uint.value := 42 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := call interpreter host in
  bytecode_result result_interpreter = Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

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
  bytecode_result result_interpreter =
    Some InstructionResult.CallNotAllowedInsideStatic \/
  result_interpreter.(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.FatalExternalError.
Proof.
  timeout 1 vm_compute.
  destruct (RuntimeFlag.is_static SpecId.PRAGUE); auto.
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
  bytecode_result result_interpreter =
    Some InstructionResult.CallNotAllowedInsideStatic \/
  is_call_frame result_interpreter.
Proof.
  timeout 1 vm_compute.
  destruct (RuntimeFlag.is_static SpecId.PRAGUE); auto.
Qed.

(** ** CREATE tests *)

Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := create false interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.StateChangeDuringStaticCall \/
  bytecode_result result_interpreter = Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  destruct (RuntimeFlag.is_static SpecId.PRAGUE); auto.
Qed.

Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};     (* value *)
    {| Uint.value := 0 |};     (* code_offset *)
    {| Uint.value := 0 |}      (* len *)
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := create false interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.StateChangeDuringStaticCall \/
  is_create_frame result_interpreter.
Proof.
  timeout 1 vm_compute.
  destruct (RuntimeFlag.is_static SpecId.PRAGUE); auto.
Qed.

(** ** CALLCODE tests *)

Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := call_code interpreter host in
  bytecode_result result_interpreter = Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

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
  timeout 1 vm_compute.
  reflexivity.
Qed.

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
  is_call_frame result_interpreter.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** DELEGATECALL tests *)

Goal
  let stack := {| Stack.value := [
    {| Uint.value := 1000 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := delegate_call interpreter host in
  bytecode_result result_interpreter = Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

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
  timeout 1 vm_compute.
  reflexivity.
Qed.

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
  is_call_frame result_interpreter.
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
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := static_call interpreter host in
  bytecode_result result_interpreter = Some InstructionResult.StackUnderflow.
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
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := static_call interpreter host in
  bytecode_result result_interpreter = Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** Tests requiring full path (FatalExternalError, call frame)
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
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that static_call with valid account creates a call frame *)
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
  is_call_frame result_interpreter.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.
