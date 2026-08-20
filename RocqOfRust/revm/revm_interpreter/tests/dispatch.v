Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.

Require Import alloy_primitives.links.aliases.
Require Import revm.revm_interpreter.instructions.simulate.table.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.simulate.dispatch.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.host.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Parameter run_InterpreterTypes_for_WIRE :
  RocqOfRust.revm.revm_interpreter.links.interpreter_types.InterpreterTypes.Run
    WIRE WIRE_types.

Definition bytecode_is_not_end (bytecode : Bytecode.t) : bool :=
  Z.ltb
    bytecode.(Bytecode.pc).(Integer.value)
    (Z.of_nat (List.length bytecode.(Bytecode.code))).

Definition run_plain_stack (code : list u8) : option (list aliases.U256.t) :=
  let interpreter :=
    make_interpreter_with_bytecode code {| Stack.value := [] |} in
  let initial_state :
      InstructionContext.State.t TestHost.t WIRE WIRE_types := {|
    InstructionContext.State.interpreter := interpreter;
    InstructionContext.State.host := TestHost.Make;
  |} in
  let table :=
    FragmentInstructionTable.table
      (H := TestHost.t)
      run_InterpreterTypes_for_WIRE in
  match
    InterpreterDispatch.run_plain_fuel
      (List.length code)
      InterpreterTypes.I
      bytecode_is_not_end
      table
      initial_state
  with
  | Some (_, {|
      InstructionContext.State.interpreter := final_interpreter;
      InstructionContext.State.host := _
    |}) =>
      Some final_interpreter.(Interpreter.stack).(Stack.value)
  | None => None
  end.

(** The executable prefix of GeneralStateTests/stExample/add11.json. *)
Goal
  run_plain_stack
    [(96 : u8); (1 : u8); (96 : u8); (1 : u8); (1 : u8); (0 : u8)] =
    Some [{| Uint.value := 2 |}].
Proof.
  timeout 5 vm_compute.
  reflexivity.
Qed.
