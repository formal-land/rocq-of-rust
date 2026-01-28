Require Import simulate.RocqOfRust.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.lt.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.gt.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.eq.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.slt.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.sgt.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.bitand.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.bitor.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.bitxor.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.iszero.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.not.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.byte.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.shl.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.shr.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.sar.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import ruint.links.lib.

(** Test that LT correctly computes 25 < 23 = false, resulting in 0 on stack *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 25 |};
    {| Uint.value := 23 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_lt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that LT correctly computes 10 < 20 = true, resulting in 1 on stack *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 10 |};
    {| Uint.value := 20 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_lt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 1 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that LT correctly computes 5 < 5 = false, resulting in 0 on stack *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 5 |};
    {| Uint.value := 5 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_lt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** GT tests *)

(** Test that GT correctly computes 25 > 23 = true, resulting in 1 on stack *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 25 |};
    {| Uint.value := 23 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_gt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 1 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that GT correctly computes 10 > 20 = false, resulting in 0 on stack *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 10 |};
    {| Uint.value := 20 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_gt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that GT correctly computes 5 > 5 = false, resulting in 0 on stack *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 5 |};
    {| Uint.value := 5 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_gt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** EQ tests *)

(** Test that EQ correctly computes 42 = 42, resulting in 1 on stack *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 42 |};
    {| Uint.value := 42 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_eq interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 1 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that EQ correctly computes 10 = 20 is false, resulting in 0 on stack *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 10 |};
    {| Uint.value := 20 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_eq interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that EQ correctly computes 0 = 0, resulting in 1 on stack *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 0 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_eq interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 1 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** SLT tests (signed less than) *)

(** Test that SLT correctly computes 5 <s 10 = true (both positive), resulting in 1 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 5 |};
    {| Uint.value := 10 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_slt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 1 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that SLT correctly computes 10 <s 5 = false (both positive), resulting in 0 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 10 |};
    {| Uint.value := 5 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_slt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that SLT correctly computes -1 <s 0 = true (negative vs positive)
    -1 in two's complement 256-bit is 2^256 - 1 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 2^256 - 1 |}; (* -1 in signed representation *)
    {| Uint.value := 0 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_slt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 1 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that SLT correctly computes 0 <s -1 = false (positive vs negative) *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 2^256 - 1 |} (* -1 in signed representation *)
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_slt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** SGT tests (signed greater than) *)

(** Test that SGT correctly computes 10 >s 5 = true (both positive), resulting in 1 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 10 |};
    {| Uint.value := 5 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_sgt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 1 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that SGT correctly computes 5 >s 10 = false (both positive), resulting in 0 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 5 |};
    {| Uint.value := 10 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_sgt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that SGT correctly computes 0 >s -1 = true (positive vs negative) *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 2^256 - 1 |} (* -1 in signed representation *)
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_sgt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 1 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that SGT correctly computes -1 >s 0 = false (negative vs positive) *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 2^256 - 1 |}; (* -1 in signed representation *)
    {| Uint.value := 0 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_sgt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** BITAND tests *)

(** Test that BITAND correctly computes 0xFF AND 0x0F = 0x0F *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 255 |};  (* 0xFF *)
    {| Uint.value := 15 |}    (* 0x0F *)
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_bitand interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 15 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that BITAND correctly computes 0 AND 123 = 0 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 123 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_bitand interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that BITAND correctly computes 42 AND 42 = 42 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 42 |};
    {| Uint.value := 42 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_bitand interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 42 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** BITOR tests *)

(** Test that BITOR correctly computes 0xF0 OR 0x0F = 0xFF *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 240 |};  (* 0xF0 *)
    {| Uint.value := 15 |}    (* 0x0F *)
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_bitor interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 255 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that BITOR correctly computes 0 OR 123 = 123 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 123 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_bitor interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 123 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that BITOR correctly computes 42 OR 42 = 42 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 42 |};
    {| Uint.value := 42 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_bitor interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 42 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** BITXOR tests *)

(** Test that BITXOR correctly computes 0xFF XOR 0x0F = 0xF0 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 255 |};  (* 0xFF *)
    {| Uint.value := 15 |}    (* 0x0F *)
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_bitxor interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 240 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that BITXOR correctly computes 123 XOR 0 = 123 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 123 |};
    {| Uint.value := 0 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_bitxor interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 123 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that BITXOR correctly computes 42 XOR 42 = 0 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 42 |};
    {| Uint.value := 42 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_bitxor interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** ISZERO tests *)

(** Test that ISZERO correctly computes ISZERO(0) = 1 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_iszero interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 1 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that ISZERO correctly computes ISZERO(1) = 0 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 1 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_iszero interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that ISZERO correctly computes ISZERO(2^256-1) = 0 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 2^256 - 1 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_iszero interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** NOT tests *)

(** Test that NOT correctly computes NOT(0) = 2^256-1 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_not interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 2^256 - 1 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that NOT correctly computes NOT(2^256-1) = 0 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 2^256 - 1 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_not interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** BYTE tests *)

(** Test that BYTE(31, 0xFF) = 0xFF *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 31 |};
    {| Uint.value := 0xFF |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_byte interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0xFF |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that BYTE(30, 0xFF00) = 0xFF *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 30 |};
    {| Uint.value :=0xFF00 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_byte interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0xFF |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that BYTE returns 0 for out of bounds index >= 32 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 32 |};
    {| Uint.value := 255 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_byte interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** SHL tests (shift left) *)

(** Test that SHL correctly computes 1 << 1 = 2 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 1 |};   (* shift amount *)
    {| Uint.value := 1 |}    (* value *)
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_shl interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 2 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that SHL correctly computes 1 << 8 = 256 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 8 |};   (* shift amount *)
    {| Uint.value := 1 |}    (* value *)
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_shl interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 256 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that SHL returns 0 for shift >= 256 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 256 |};  (* shift amount >= 256 *)
    {| Uint.value := 1 |}     (* value *)
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_shl interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** SHR tests (logical shift right) *)

(** Test that SHR correctly computes 256 >> 1 = 128 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 1 |};    (* shift amount *)
    {| Uint.value := 256 |}   (* value *)
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_shr interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 128 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that SHR correctly computes 256 >> 8 = 1 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 8 |};    (* shift amount *)
    {| Uint.value := 256 |}   (* value *)
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_shr interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 1 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that SHR returns 0 for shift >= 256 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 256 |};  (* shift amount >= 256 *)
    {| Uint.value := 1 |}     (* value *)
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_shr interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** SAR tests (arithmetic shift right) *)

(** Test that SAR correctly computes 256 >>s 1 = 128 (positive value) *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 1 |};    (* shift amount *)
    {| Uint.value := 256 |}   (* value *)
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_sar interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 128 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that SAR correctly computes (-1) >>s 1 = -1 (all 1s stays all 1s) *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 1 |};           (* shift amount *)
    {| Uint.value := 2^256 - 1 |}    (* -1 in two's complement *)
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_sar interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 2^256 - 1 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that SAR correctly computes (-2) >>s 1 = -1 *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 1 |};           (* shift amount *)
    {| Uint.value := 2^256 - 2 |}    (* -2 in two's complement *)
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_sar interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 2^256 - 1 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that SAR returns 0 for large shift on positive value *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 256 |};  (* shift amount >= 256 *)
    {| Uint.value := 100 |}   (* positive value *)
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_sar interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.
