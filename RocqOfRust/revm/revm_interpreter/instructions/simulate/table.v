Require Import links.RocqOfRust.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.instructions.links.arithmetic.
Require Import revm.revm_interpreter.instructions.links.control.stop.
Require Import revm.revm_interpreter.instructions.links.control.unknown.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.links.table.

Module FragmentInstructionTable.
  Definition stop_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_stop run_InterpreterTypes_for_WIRE context).

  Definition add_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_add run_InterpreterTypes_for_WIRE context).

  Definition sub_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_sub run_InterpreterTypes_for_WIRE context).

  Definition mul_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_mul run_InterpreterTypes_for_WIRE context).

  Definition unknown_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_unknown run_InterpreterTypes_for_WIRE context).

  Definition table
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    array.t
      (Instruction.t WIRE H WIRE_types)
      {| Integer.value := 256 |} :=
    let unknown_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        unknown_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 0 |};
    |} in
    let stop_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        stop_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 0 |};
    |} in
    let add_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        add_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let sub_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        sub_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let mul_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        mul_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 5 |};
    |} in
    @array.Build_t
      (Instruction.t WIRE H WIRE_types)
      {| Integer.value := 256 |}
      (
        ArrayPair.Build_t
          stop_instruction
          (ArrayPair.Build_t
            add_instruction
            (ArrayPair.Build_t
              mul_instruction
              (ArrayPair.Build_t
                sub_instruction
                (ArrayPairs.repeat unknown_instruction 252))))
      ).
End FragmentInstructionTable.
