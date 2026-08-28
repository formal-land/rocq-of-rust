Require Import simulate.RocqOfRust.
Require Import revm.revm_interpreter.instructions.simulate.control.stop.
Require Import revm.revm_interpreter.instructions.simulate.control.invalid.
Require Import revm.revm_interpreter.instructions.simulate.control.unknown.
Require Import revm.revm_interpreter.instructions.simulate.control.jump.
Require Import revm.revm_interpreter.instructions.simulate.control.jump_inner.
Require Import revm.revm_interpreter.instructions.simulate.control.jumpi.
Require Import revm.revm_interpreter.instructions.simulate.control.pc.
Require Import revm.revm_interpreter.instructions.simulate.control.ret.
Require Import revm.revm_interpreter.instructions.simulate.control.revert.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.interpreter_InterpreterResult.
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

(** ** STOP tests *)

(** Test that STOP sets instruction_result to Stop *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let result := stop interpreter in
  bytecode_result result = Some InstructionResult.Stop.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** INVALID tests *)

(** Test that INVALID sets instruction_result to InvalidFEOpcode *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let result := invalid interpreter in
  bytecode_result result = Some InstructionResult.InvalidFEOpcode.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** UNKNOWN tests *)

(** Test that UNKNOWN sets instruction_result to OpcodeNotFound *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let result := unknown interpreter in
  bytecode_result result = Some InstructionResult.OpcodeNotFound.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** RET tests *)

(** Test that RET with offset=0, len=0 sets instruction_result to Return *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 0 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := ret interpreter in
  bytecode_result result = Some InstructionResult.Return.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that RET with offset=0, len=0 sets next_action to Return *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 0 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := ret interpreter in
  match bytecode_action result with
  | Some (InterpreterAction.Return _) => True
  | _ => False
  end.
Proof.
  timeout 1 vm_compute.
  exact I.
Qed.

(** ** REVERT tests *)

(** Test that REVERT with offset=0, len=0 sets instruction_result to Revert *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 0 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := revert interpreter in
  bytecode_result result = Some InstructionResult.Revert.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** PC tests *)

(** Test that PC pushes pc-1 onto the stack.
    With test bytecode pc = 0, this wraps to usize::MAX. *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let result := pc interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 18446744073709551615 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** JUMP tests *)

Definition valid_legacy_jump (code : list u8) (offset : Z) : bool :=
  let interpreter :=
    make_interpreter_with_bytecode code {| Stack.value := [] |} in
  fst
    (Jumps.is_valid_legacy_jump
      interpreter.(Interpreter.bytecode)
      {| Integer.value := offset |}).

Goal valid_legacy_jump [(91 : u8)] 0 = true.
Proof. timeout 1 vm_compute. reflexivity. Qed.

Goal valid_legacy_jump [(0 : u8)] 0 = false.
Proof. timeout 1 vm_compute. reflexivity. Qed.

Goal valid_legacy_jump [(91 : u8)] 1 = false.
Proof. timeout 1 vm_compute. reflexivity. Qed.

(** A JUMPDEST byte inside PUSH data is not an instruction boundary. *)
Goal valid_legacy_jump [(97 : u8); (0 : u8); (91 : u8); (91 : u8)] 2 = false.
Proof. timeout 1 vm_compute. reflexivity. Qed.

Goal valid_legacy_jump [(97 : u8); (0 : u8); (91 : u8); (91 : u8)] 3 = true.
Proof. timeout 1 vm_compute. reflexivity. Qed.

Goal
  valid_legacy_jump
    ([(127 : u8)] ++ List.repeat (91 : u8) 32 ++ [(91 : u8)])
    32 = false.
Proof. timeout 1 vm_compute. reflexivity. Qed.

Goal
  valid_legacy_jump
    ([(127 : u8)] ++ List.repeat (91 : u8) 32 ++ [(91 : u8)])
    33 = true.
Proof. timeout 1 vm_compute. reflexivity. Qed.

(** Test that JUMP with valid target succeeds *)
Goal
  let stack := {| Stack.value := [{| Uint.value := 0 |}] |} in
  let interpreter := make_interpreter_with_bytecode [(91 : u8)] stack in
  let result := jump interpreter in
  bytecode_result result = None.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that JUMP pops the target from stack *)
Goal
  let stack := {| Stack.value := [{| Uint.value := 0 |}] |} in
  let interpreter := make_interpreter_with_bytecode [(91 : u8)] stack in
  let result := jump interpreter in
  result.(Interpreter.stack).(Stack.value) = [].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that JUMP rejects a non-JUMPDEST target *)
Goal
  let stack := {| Stack.value := [{| Uint.value := 0 |}] |} in
  let interpreter := make_interpreter_with_bytecode [(0 : u8)] stack in
  let result := jump interpreter in
  bytecode_result result = Some InstructionResult.InvalidJump.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that JUMP with empty stack gives StackUnderflow *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let result := jump interpreter in
  bytecode_result result = Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** JUMPI tests *)

(** Test that JUMPI with cond=0 does not jump *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 5 |};
    {| Uint.value := 0 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := jumpi interpreter in
  bytecode_result result = None.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that JUMPI with cond=0 pops both values *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 5 |};
    {| Uint.value := 0 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := jumpi interpreter in
  result.(Interpreter.stack).(Stack.value) = [].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that JUMPI with cond=1 takes the jump *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 1 |}
  ] |} in
  let interpreter := make_interpreter_with_bytecode [(91 : u8)] stack in
  let result := jumpi interpreter in
  bytecode_result result = None.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** A taken JUMPI rejects a JUMPDEST byte inside PUSH data. *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 2 |};
    {| Uint.value := 1 |}
  ] |} in
  let interpreter :=
    make_interpreter_with_bytecode
      [(97 : u8); (0 : u8); (91 : u8); (91 : u8)]
      stack in
  let result := jumpi interpreter in
  bytecode_result result = Some InstructionResult.InvalidJump.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** Test that JUMPI with empty stack gives StackUnderflow *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let result := jumpi interpreter in
  bytecode_result result = Some InstructionResult.StackUnderflow.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** JUMP_INNER tests *)

(** Test that JUMP_INNER with valid target succeeds *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter_with_bytecode [(91 : u8)] stack in
  let target : aliases.U256.t := {| Uint.value := 0 |} in
  let result := jump_inner interpreter target in
  bytecode_result result = None.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.
