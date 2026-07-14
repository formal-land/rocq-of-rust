Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.log.links.mod.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.instructions.simulate.host.balance.
Require Import revm.revm_interpreter.instructions.simulate.host.blockhash.
Require Import revm.revm_interpreter.instructions.simulate.host.extcodecopy.
Require Import revm.revm_interpreter.instructions.simulate.host.extcodehash.
Require Import revm.revm_interpreter.instructions.simulate.host.extcodesize.
Require Import revm.revm_interpreter.instructions.simulate.host.log.
Require Import revm.revm_interpreter.instructions.simulate.host.selfbalance.
Require Import revm.revm_interpreter.instructions.simulate.host.selfdestruct.
Require Import revm.revm_interpreter.instructions.simulate.host.sload.
Require Import revm.revm_interpreter.instructions.simulate.host.sstore.
Require Import revm.revm_interpreter.instructions.simulate.host.tload.
Require Import revm.revm_interpreter.instructions.simulate.host.tstore.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.interpreter_InterpreterResult.
Require Import revm.revm_interpreter.tests.host.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import ruint.links.lib.

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

(** ** BALANCE *)

Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := balance interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

Goal
  let stack := {| Stack.value := [{| Uint.value := 0 |}] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := balance interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.FatalExternalError.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** BLOCKHASH *)

Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := blockhash interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  trivial.
Qed.

Goal
  let stack := {| Stack.value := [{| Uint.value := 0 |}] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := blockhash interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.FatalExternalError.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** EXTCODECOPY / EXTCODEHASH / EXTCODESIZE *)

Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := extcodecopy interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |}; {| Uint.value := 0 |};
    {| Uint.value := 0 |}; {| Uint.value := 0 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := extcodecopy interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.FatalExternalError.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

Goal
  let stack := {| Stack.value := [{| Uint.value := 0 |}] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := extcodehash interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.FatalExternalError.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

Goal
  let stack := {| Stack.value := [{| Uint.value := 0 |}] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := extcodesize interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.FatalExternalError.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** LOG *)

Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := log {| Integer.value := 0 |} interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.StateChangeDuringStaticCall \/
  bytecode_result result_interpreter =
    Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  repeat match goal with
  | |- context [RuntimeFlag.is_static ?x] => destruct (RuntimeFlag.is_static x)
  end; auto.
Qed.

Goal
  let stack := {| Stack.value := [{| Uint.value := 0 |}; {| Uint.value := 0 |}] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := log {| Integer.value := 0 |} interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.StateChangeDuringStaticCall \/
  result_interpreter.(Interpreter.control).(Control.instruction_result) = None.
Proof.
  timeout 1 vm_compute.
  repeat match goal with
  | |- context [RuntimeFlag.is_static ?x] => destruct (RuntimeFlag.is_static x)
  end; auto.
Qed.

(** ** SELFBALANCE *)

Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := selfbalance interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.FatalExternalError.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** SELFDESTRUCT *)

Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := selfdestruct interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.StateChangeDuringStaticCall \/
  bytecode_result result_interpreter =
    Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  repeat match goal with
  | |- context [RuntimeFlag.is_static ?x] => destruct (RuntimeFlag.is_static x)
  end; auto.
Qed.

Goal
  let stack := {| Stack.value := [{| Uint.value := 0 |}] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := selfdestruct interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.StateChangeDuringStaticCall \/
  bytecode_result result_interpreter =
    Some InstructionResult.FatalExternalError.
Proof.
  timeout 1 vm_compute.
  repeat match goal with
  | |- context [RuntimeFlag.is_static ?x] => destruct (RuntimeFlag.is_static x)
  end; auto.
Qed.

(** ** SLOAD / SSTORE *)

Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := sload interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

Goal
  let stack := {| Stack.value := [{| Uint.value := 0 |}] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := sload interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.FatalExternalError.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := sstore interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.StateChangeDuringStaticCall \/
  bytecode_result result_interpreter =
    Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  repeat match goal with
  | |- context [RuntimeFlag.is_static ?x] => destruct (RuntimeFlag.is_static x)
  end; auto.
Qed.

Goal
  let stack := {| Stack.value := [{| Uint.value := 0 |}; {| Uint.value := 0 |}] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := sstore interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.StateChangeDuringStaticCall \/
  bytecode_result result_interpreter =
    Some InstructionResult.FatalExternalError.
Proof.
  timeout 1 vm_compute.
  repeat match goal with
  | |- context [RuntimeFlag.is_static ?x] => destruct (RuntimeFlag.is_static x)
  end; auto.
Qed.

(** ** TLOAD / TSTORE *)

Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := tload interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

Goal
  let stack := {| Stack.value := [{| Uint.value := 7 |}] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := tload interpreter host in
  result_interpreter.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := tstore interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.StateChangeDuringStaticCall \/
  bytecode_result result_interpreter =
    Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  repeat match goal with
  | |- context [RuntimeFlag.is_static ?x] => destruct (RuntimeFlag.is_static x)
  end; auto.
Qed.

Goal
  let stack := {| Stack.value := [{| Uint.value := 0 |}; {| Uint.value := 0 |}] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := tstore interpreter host in
  bytecode_result result_interpreter =
    Some InstructionResult.StateChangeDuringStaticCall \/
  result_interpreter.(Interpreter.control).(Control.instruction_result) = None.
Proof.
  timeout 1 vm_compute.
  repeat match goal with
  | |- context [RuntimeFlag.is_static ?x] => destruct (RuntimeFlag.is_static x)
  end; auto.
Qed.
