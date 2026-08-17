Require Import links.RocqOfRust.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.instructions.links.arithmetic.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.addmod.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.div.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.rem.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.sdiv.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.smod.
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

  Definition div_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_div run_InterpreterTypes_for_WIRE context).

  Definition sdiv_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_sdiv run_InterpreterTypes_for_WIRE context).

  Definition mod_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_rem run_InterpreterTypes_for_WIRE context).

  Definition smod_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_smod run_InterpreterTypes_for_WIRE context).

  Definition addmod_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_addmod run_InterpreterTypes_for_WIRE context).

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
    let div_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        div_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 5 |};
    |} in
    let sdiv_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        sdiv_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 5 |};
    |} in
    let mod_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        mod_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 5 |};
    |} in
    let smod_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        smod_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 5 |};
    |} in
    let addmod_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        addmod_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 8 |};
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
                (ArrayPair.Build_t
                  div_instruction
                  (ArrayPair.Build_t
                    sdiv_instruction
                    (ArrayPair.Build_t
                      mod_instruction
                      (ArrayPair.Build_t
                      smod_instruction
                        (ArrayPair.Build_t
                          addmod_instruction
                          (ArrayPairs.repeat unknown_instruction 247)))))))))
      ).
End FragmentInstructionTable.
