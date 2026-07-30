Require Import simulate.RocqOfRust.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.

Module InstructionContext.
  Record State
      (H WIRE : Set) `{Link H} `{Link WIRE}
      (WIRE_types : InterpreterTypes.Types.t)
      `{InterpreterTypes.Types.AreLinks WIRE_types} : Set := {
    state_interpreter : Interpreter.t WIRE WIRE_types;
    state_host : H;
  }.

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
      (_state : State H WIRE WIRE_types) :
      instruction_context.InstructionContext.t H WIRE WIRE_types :=
    make.

  Definition map_interpreter
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (f :
        Interpreter.t WIRE WIRE_types ->
        Interpreter.t WIRE WIRE_types)
      (state : State H WIRE WIRE_types) :
      State H WIRE WIRE_types :=
    match state with
    | {| state_interpreter := interpreter; state_host := host |} =>
        {|
          state_interpreter := f interpreter;
          state_host := host;
        |}
    end.
End InstructionContext.
