Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import RocqOfRust.lib.simulate.lib.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import ruint.links.lib.

(** Test that ADD correctly computes 10 + 20 = 30 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 10 |};
    {| Uint.value := 20 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := arithmetic.add interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 30 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that ADD correctly handles overflow (wrapping) *)
Goal
  let max_val := 2 ^ 256 - 1 in
  let stack := {| Stack.value := [
    {| Uint.value := max_val |};
    {| Uint.value := 1 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := arithmetic.add interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that SUB correctly computes 50 - 30 = 20 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 50 |};
    {| Uint.value := 30 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := arithmetic.sub interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 20 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that SUB correctly handles underflow (wrapping) *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 1 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := arithmetic.sub interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 2 ^ 256 - 1 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that MUL correctly computes 6 * 7 = 42 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 6 |};
    {| Uint.value := 7 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := arithmetic.mul interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 42 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that MUL correctly handles overflow (wrapping) *)
Goal
  let half := 2 ^ 255 in
  let stack := {| Stack.value := [
    {| Uint.value := half |};
    {| Uint.value := 2 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := arithmetic.mul interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that DIV correctly computes 100 / 5 = 20 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 100 |};
    {| Uint.value := 5 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := arithmetic.div interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 20 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that DIV by zero leaves stack unchanged (EVM behavior) *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 100 |};
    {| Uint.value := 0 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := arithmetic.div interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that DIV truncates (integer division): 7 / 3 = 2 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 7 |};
    {| Uint.value := 3 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := arithmetic.div interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 2 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.
