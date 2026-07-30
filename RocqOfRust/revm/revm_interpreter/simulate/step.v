Require Import Stdlib.Lists.List.

Require Import simulate.RocqOfRust.
Require Import core.links.array.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.links.table.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.simulate.interpreter.
Require Import revm.revm_interpreter.simulate.interpreter_types.

Module InterpreterStep.
  Module Preparation.
    Inductive t
        (H WIRE : Set) `{Link H} `{Link WIRE}
        (WIRE_types : InterpreterTypes.Types.t)
        `{InterpreterTypes.Types.AreLinks WIRE_types} : Set :=
    | OutOfGas (state : InstructionContext.State.t H WIRE WIRE_types)
    | Ready
        (opcode : u8)
        (instruction : Instruction.t WIRE H WIRE_types)
        (state : InstructionContext.State.t H WIRE WIRE_types).

    Arguments OutOfGas {_ _ _ _ _ _} _.
    Arguments Ready {_ _ _ _ _ _} _ _ _.
  End Preparation.

  Definition instruction_at
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (table :
        array.t
          (Instruction.t WIRE H WIRE_types)
          {| Integer.value := 256 |})
      (opcode : u8) : option (Instruction.t WIRE H WIRE_types) :=
    List.nth_error
      (ArrayPairs.to_list table.(array.value))
      (Z.to_nat opcode.(Integer.value)).

  Definition instruction_static_gas
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (instruction : Instruction.t WIRE H WIRE_types) : u64 :=
    let '{| Instruction.static_gas := static_gas |} := instruction in
    static_gas.

  Definition prepare
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (IInterpreterTypes : InterpreterTypes.C WIRE_types)
      (table :
        array.t
          (Instruction.t WIRE H WIRE_types)
          {| Integer.value := 256 |})
      (state : InstructionContext.State.t H WIRE WIRE_types) :
      option (Preparation.t H WIRE WIRE_types) :=
    match state with
    | {|
        InstructionContext.State.interpreter := interpreter;
        InstructionContext.State.host := host
      |} =>
        let jumps :=
          IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode) in
        let opcode := jumps.(Jumps.opcode) interpreter.(Interpreter.bytecode) in
        let bytecode :=
          jumps.(Jumps.relative_jump)
            interpreter.(Interpreter.bytecode)
            {| Integer.value := 1 |} in
        let interpreter :=
          interpreter <| Interpreter.bytecode := bytecode |> in
        match instruction_at table opcode with
        | None => None
        | Some instruction =>
            match
              Impl_Gas.record_cost
                interpreter.(Interpreter.gas)
                (instruction_static_gas instruction)
            with
            | None =>
                Some
                  (Preparation.OutOfGas {|
                    InstructionContext.State.interpreter :=
                      halt_oog interpreter;
                    InstructionContext.State.host := host;
                  |})
            | Some gas =>
                Some
                  (Preparation.Ready
                    opcode
                    instruction
                    {|
                      InstructionContext.State.interpreter :=
                        interpreter <| Interpreter.gas := gas |>;
                      InstructionContext.State.host := host;
                    |})
            end
        end
    end.

  Definition Dispatch
      (H WIRE : Set) `{Link H} `{Link WIRE}
      (WIRE_types : InterpreterTypes.Types.t)
      `{InterpreterTypes.Types.AreLinks WIRE_types} : Set :=
    u8 ->
    InstructionContext.State.t H WIRE WIRE_types ->
    InstructionContext.State.t H WIRE WIRE_types.

  Module Result.
    Inductive t
        (H WIRE : Set) `{Link H} `{Link WIRE}
        (WIRE_types : InterpreterTypes.Types.t)
        `{InterpreterTypes.Types.AreLinks WIRE_types} : Set :=
    | MissingInstruction
    | OutOfGas (state : InstructionContext.State.t H WIRE WIRE_types)
    | Success (state : InstructionContext.State.t H WIRE WIRE_types).

    Arguments MissingInstruction {_ _ _ _ _ _}.
    Arguments OutOfGas {_ _ _ _ _ _} _.
    Arguments Success {_ _ _ _ _ _} _.
  End Result.

  Definition step_result
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (IInterpreterTypes : InterpreterTypes.C WIRE_types)
      (dispatch : Dispatch H WIRE WIRE_types)
      (table :
        array.t
          (Instruction.t WIRE H WIRE_types)
          {| Integer.value := 256 |})
      (state : InstructionContext.State.t H WIRE WIRE_types) :
      Result.t H WIRE WIRE_types :=
    match prepare IInterpreterTypes table state with
    | None => Result.MissingInstruction
    | Some (Preparation.OutOfGas state) => Result.OutOfGas state
    | Some (Preparation.Ready opcode _ state) =>
        Result.Success (dispatch opcode state)
    end.
End InterpreterStep.
