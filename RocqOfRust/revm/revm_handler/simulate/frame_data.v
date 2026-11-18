Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.log.links.mod.
Require Import core.ops.links.range.
Require Import revm.revm_interpreter.links.interpreter_InterpreterResult.

Module CallOutcome.
  Record t : Set := {
    result : InterpreterResult.t;
    memory_offset : Range.t usize;
    was_precompile_called : bool;
    precompile_call_logs : list (Log.t LogData.t);
  }.

  Definition new (result : InterpreterResult.t) (memory_offset : Range.t usize) : t := {|
    result := result; memory_offset := memory_offset;
    was_precompile_called := false; precompile_call_logs := [];
  |}.
End CallOutcome.

Module CreateOutcome.
  Record t : Set := {
    result : InterpreterResult.t;
    address : option Address.t;
  }.
End CreateOutcome.

Module CallFrame.
  Record t : Set := { return_memory_range : Range.t usize }.
End CallFrame.

Module CreateFrame.
  Record t : Set := { created_address : Address.t }.
End CreateFrame.

Module FrameData.
  Inductive t : Set :=
  | Call (frame : CallFrame.t)
  | Create (frame : CreateFrame.t).
End FrameData.

Module FrameResult.
  Inductive t : Set :=
  | Call (outcome : CallOutcome.t)
  | Create (outcome : CreateOutcome.t).

  Definition into_interpreter_result (self : t) :=
    match self with
    | Call outcome => outcome.(CallOutcome.result)
    | Create outcome => outcome.(CreateOutcome.result)
    end.
  Definition map_interpreter_result (f : InterpreterResult.t -> InterpreterResult.t) (self : t) : t :=
    match self with
    | Call outcome => Call (outcome <| CallOutcome.result := f outcome.(CallOutcome.result) |>)
    | Create outcome => Create (outcome <| CreateOutcome.result := f outcome.(CreateOutcome.result) |>)
    end.
End FrameResult.
