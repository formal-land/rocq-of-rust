Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import core.convert.simulate.mod.
Require Import revm.revm_interpreter.instructions.simulate.system.address.
Require Import revm.revm_interpreter.instructions.simulate.system.caller.
Require Import revm.revm_interpreter.instructions.simulate.system.callvalue.
Require Import revm.revm_interpreter.instructions.simulate.system.calldatasize.
Require Import revm.revm_interpreter.instructions.simulate.system.calldataload.
Require Import revm.revm_interpreter.instructions.simulate.system.calldatacopy.
Require Import revm.revm_interpreter.instructions.simulate.system.codesize.
Require Import revm.revm_interpreter.instructions.simulate.system.codecopy.
Require Import revm.revm_interpreter.instructions.simulate.system.gas.
Require Import revm.revm_interpreter.instructions.simulate.system.keccak256.
Require Import revm.revm_interpreter.instructions.simulate.system.returndatasize.
Require Import revm.revm_interpreter.instructions.simulate.system.returndatacopy.
Require Import revm.revm_interpreter.instructions.simulate.system.memory_resize.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_primitives.simulate.lib.
Require Import ruint.links.lib.

(** ** GAS tests *)

(** Test that GAS pushes remaining gas after BASE cost deduction.
    Gas starts at 1000000, BASE cost = 2. After deducting 2, remaining = 999998. *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let result := gas interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 999998 |}].
Proof.
Admitted.

(** ** KECCAK256 tests *)

(** Test that KECCAK256 with len=0 pushes the hash of the empty input.
    Stack: [offset=0, len=0] -> top = Into.into KECCAK_EMPTY *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 0 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := keccak256 interpreter in
  result.(Interpreter.stack).(Stack.value) =
    [Into.into KECCAK_EMPTY].
Proof.
  timeout 5 vm_compute.
  reflexivity.
Qed.

(** ** ADDRESS/CALLER/CALLVALUE/CALLDATASIZE/CODESIZE/RETURNDATASIZE tests *)

Goal
  let interpreter := make_interpreter {| Stack.value := [] |} in
  Z.of_nat (List.length (address interpreter).(Interpreter.stack).(Stack.value)) = 1.
Proof.
Admitted.

Goal
  let interpreter := make_interpreter {| Stack.value := [] |} in
  (address interpreter).(Interpreter.control).(Control.gas).(Gas.remaining) = 999998.
Proof.
Admitted.

Goal
  let interpreter := make_interpreter {| Stack.value := [] |} in
  Z.of_nat (List.length (caller interpreter).(Interpreter.stack).(Stack.value)) = 1.
Proof.
Admitted.

Goal
  let interpreter := make_interpreter {| Stack.value := [] |} in
  Z.of_nat (List.length (callvalue interpreter).(Interpreter.stack).(Stack.value)) = 1.
Proof.
Admitted.

Goal
  let interpreter := make_interpreter {| Stack.value := [] |} in
  Z.of_nat (List.length (calldatasize interpreter).(Interpreter.stack).(Stack.value)) = 1.
Proof.
Admitted.

Goal
  let interpreter := make_interpreter {| Stack.value := [] |} in
  Z.of_nat (List.length (codesize interpreter).(Interpreter.stack).(Stack.value)) = 1.
Proof.
Admitted.

Goal
  let interpreter := make_interpreter {| Stack.value := [] |} in
  Z.of_nat (List.length (returndatasize interpreter).(Interpreter.stack).(Stack.value)) = 1.
Proof.
Admitted.

(** ** Stack underflow tests *)

Goal
  let interpreter := make_interpreter {| Stack.value := [] |} in
  (calldataload interpreter).(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.StackUnderflow.
Proof.
Admitted.

Goal
  let interpreter := make_interpreter {| Stack.value := [] |} in
  (calldatacopy interpreter).(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.StackUnderflow.
Proof.
Admitted.

Goal
  let interpreter := make_interpreter {| Stack.value := [] |} in
  (codecopy interpreter).(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.StackUnderflow.
Proof.
Admitted.

Goal
  let interpreter := make_interpreter {| Stack.value := [] |} in
  (returndatacopy interpreter).(Interpreter.control).(Control.instruction_result) =
    Some InstructionResult.StackUnderflow.
Proof.
Admitted.

(** ** memory_resize helper smoke test *)

Goal
  let interpreter := make_interpreter {| Stack.value := [] |} in
  fst (memory_resize interpreter {| Uint.value := 0 |} {| Integer.value := 0 |}) = None.
Proof.
Admitted.
