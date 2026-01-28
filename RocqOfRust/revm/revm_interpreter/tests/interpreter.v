Require Import simulate.RocqOfRust.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.tests.interpreter_types.

Definition make_interpreter (stack : Stack.t) : Interpreter.t WIRE WIRE_types := {|
  Interpreter.bytecode := tt;
  Interpreter.stack := stack;
  Interpreter.return_data := tt;
  Interpreter.memory := tt;
  Interpreter.input := tt;
  Interpreter.sub_routine := tt;
  Interpreter.control := {|
    Control.gas := {|
      Gas.limit := 1000000;
      Gas.memory := {|
        MemoryGas.expansion_cost := 10;
        MemoryGas.words_num := 12;
      |};
      Gas.refunded := 0;
      Gas.remaining := 1000000;
    |};
    Control.instruction_result := None;
  |};
  Interpreter.runtime_flag := tt;
  Interpreter.extend := tt;
|}.
