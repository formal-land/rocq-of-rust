Require Import simulate.RocqOfRust.
Require Import revm.revm_interpreter.instructions.simulate.tx_info.gasprice.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.tests.host.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import ruint.links.lib.

(** ** GASPRICE tests *)

(** Test that GASPRICE pushes the effective gas price (= 42) onto the stack *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := gasprice interpreter host in
  result_interpreter.(Interpreter.stack).(Stack.value) = [{| Uint.value := 42 |}].
Proof.
Admitted.

(** Test that GASPRICE does not set an error *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := gasprice interpreter host in
  result_interpreter.(Interpreter.control).(Control.instruction_result) = None.
Proof.
Admitted.
