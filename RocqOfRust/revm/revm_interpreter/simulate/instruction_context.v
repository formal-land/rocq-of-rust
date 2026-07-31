Require Import simulate.RocqOfRust.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.

Module InstructionContext.
  Module State.
    Record t
        (H WIRE : Set) `{Link H} `{Link WIRE}
        (WIRE_types : InterpreterTypes.Types.t)
        `{InterpreterTypes.Types.AreLinks WIRE_types} : Set := {
      interpreter : Interpreter.t WIRE WIRE_types;
      host : H;
    }.
  End State.

  Definition make
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types} :
      instruction_context.InstructionContext.t H WIRE WIRE_types :=
    {|
      instruction_context.InstructionContext.interpreter := make_ref 0;
      instruction_context.InstructionContext.host := make_ref 1;
    |}.

  Definition context
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (_state : State.t H WIRE WIRE_types) :
      instruction_context.InstructionContext.t H WIRE WIRE_types :=
    make.

  Definition map_interpreter
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (f :
        Interpreter.t WIRE WIRE_types ->
        Interpreter.t WIRE WIRE_types)
      (state : State.t H WIRE WIRE_types) :
      State.t H WIRE WIRE_types :=
    match state with
    | {| State.interpreter := interpreter; State.host := host |} =>
        {|
          State.interpreter := f interpreter;
          State.host := host;
        |}
    end.
End InstructionContext.
