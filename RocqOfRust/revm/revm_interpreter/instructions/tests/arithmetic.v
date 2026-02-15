Require Import simulate.RocqOfRust.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.add.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.addmod.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.div.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.exp.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.mul.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.mulmod.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.rem.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.sdiv.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.signextend.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.smod.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.sub.
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
  let result := add interpreter in
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
  let result := add interpreter in
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
  let result := sub interpreter in
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
  let result := sub interpreter in
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
  let result := mul interpreter in
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
  let result := mul interpreter in
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
  let result := div interpreter in
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
  let result := div interpreter in
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
  let result := div interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 2 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** REM tests *)

(** Test that REM correctly computes 10 % 3 = 1 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 10 |};
    {| Uint.value := 3 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := rem interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 1 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that REM by zero returns 0 (EVM behavior: divisor is zero, is_zero check skips) *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 10 |};
    {| Uint.value := 0 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := rem interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** SDIV tests (signed division) *)

(** Test that SDIV correctly computes 6 /s 3 = 2 (both positive) *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 6 |};
    {| Uint.value := 3 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := sdiv interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 2 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** SMOD tests (signed modulo) *)

(** Test that SMOD correctly computes 10 %s 3 = 1 (both positive) *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 10 |};
    {| Uint.value := 3 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := smod interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 1 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** ADDMOD tests *)

(** Test that ADDMOD correctly computes (10 + 10) % 8 = 4 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 10 |};
    {| Uint.value := 10 |};
    {| Uint.value := 8 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := addmod interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 4 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** MULMOD tests *)

(** Test that MULMOD correctly computes (10 * 10) % 8 = 4 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 10 |};
    {| Uint.value := 10 |};
    {| Uint.value := 8 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := mulmod interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 4 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** EXP tests *)

(** Test that EXP correctly computes 2 ^ 10 = 1024 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 2 |};
    {| Uint.value := 10 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := exp InterpreterTypes.I interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 1024 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** SIGNEXTEND tests *)

(** Test that SIGNEXTEND(0, 0x7F) = 0x7F (positive byte, no sign extension) *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 127 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := signextend interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 127 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that SIGNEXTEND(0, 0xFF) = 2^256-1 (negative byte sign-extends to all 1s) *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 255 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := signextend interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 2 ^ 256 - 1 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.
