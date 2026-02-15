Require Import simulate.RocqOfRust.
Require Import revm.revm_interpreter.instructions.simulate.memory.msize.
Require Import revm.revm_interpreter.instructions.simulate.memory.mstore.
Require Import revm.revm_interpreter.instructions.simulate.memory.mload.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import ruint.links.lib.

(** ** MSIZE tests *)

(** Test that MSIZE pushes 0 on an empty memory *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let result := msize interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** MSTORE tests *)

(** Test that MSTORE with offset 0 and value 42 empties the stack and writes to memory *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 42 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := mstore interpreter in
  result.(Interpreter.stack).(Stack.value) = [].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** MLOAD tests *)

(** Helper to build an interpreter with a given stack and memory *)
Definition make_interpreter_with_memory (stack : Stack.t) (memory : Memory.t)
    (gas_val : Gas.t) : Interpreter.t WIRE WIRE_types := {|
  Interpreter.bytecode := tt;
  Interpreter.stack := stack;
  Interpreter.return_data := tt;
  Interpreter.memory := memory;
  Interpreter.input := tt;
  Interpreter.sub_routine := tt;
  Interpreter.control := {|
    Control.gas := gas_val;
    Control.instruction_result := None;
    Control.next_action := None;
  |};
  Interpreter.runtime_flag := SpecId.LATEST;
  Interpreter.extend := tt;
|}.

(** Test that MSTORE followed by MLOAD roundtrips: store 42 at offset 0, then load *)
Goal
  let stack_store := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 42 |}
  ] |} in
  let interpreter := make_interpreter stack_store in
  let after_store := mstore interpreter in
  (* Build a new interpreter reusing the memory and gas from after_store *)
  let stack_load := {| Stack.value := [{| Uint.value := 0 |}] |} in
  let interpreter_for_load :=
    make_interpreter_with_memory stack_load
      after_store.(Interpreter.memory)
      after_store.(Interpreter.control).(Control.gas) in
  let after_load := mload interpreter_for_load in
  after_load.(Interpreter.stack).(Stack.value) = [{| Uint.value := 42 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.
