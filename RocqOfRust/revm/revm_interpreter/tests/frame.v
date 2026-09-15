Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import simulate.RocqOfRust.

Module StatefulFrame.
  Definition successful (result : InstructionResult.t) : bool :=
    match result with
    | InstructionResult.Stop
    | InstructionResult.Return
    | InstructionResult.SelfDestruct => true
    | _ => false
    end.

  (** The snapshot is taken after entry warming. This finalizes only a returned
      frame; a pending child frame and an incomplete run remain unchanged. *)
  Definition finish (checkpoint : StatefulHost.t)
      (result : option
        (InterpreterAction.t *
          InstructionContext.State.t StatefulHost.t WIRE WIRE_types)) :=
    match result with
    | Some (action, state) =>
        let state :=
          match action with
          | InterpreterAction.Return output =>
              if successful output.(InterpreterResult.result) then state
              else state <| @InstructionContext.State.host
                StatefulHost.t WIRE _ _ WIRE_types _ := checkpoint |>
          | InterpreterAction.NewFrame _ => state
          end in
        Some (action, state)
    | None => None
    end.

  Lemma incomplete_stays_incomplete (checkpoint : StatefulHost.t) :
    finish checkpoint None = None.
  Proof. reflexivity. Qed.

  Lemma failed_frame_restores_host
      (checkpoint : StatefulHost.t)
      (state : InstructionContext.State.t StatefulHost.t WIRE WIRE_types)
      (output : InterpreterResult.t)
      (H_failed : successful output.(InterpreterResult.result) = false) :
    finish checkpoint (Some (InterpreterAction.Return output, state)) =
    Some (InterpreterAction.Return output,
      state <| @InstructionContext.State.host
        StatefulHost.t WIRE _ _ WIRE_types _ := checkpoint |>).
  Proof. unfold finish. now rewrite H_failed. Qed.

  Lemma successful_frame_keeps_host
      (checkpoint : StatefulHost.t)
      (state : InstructionContext.State.t StatefulHost.t WIRE WIRE_types)
      (output : InterpreterResult.t)
      (H_success : successful output.(InterpreterResult.result) = true) :
    finish checkpoint (Some (InterpreterAction.Return output, state)) =
    Some (InterpreterAction.Return output, state).
  Proof. unfold finish. now rewrite H_success. Qed.

  Lemma suspended_frame_stays_suspended
      (checkpoint : StatefulHost.t)
      (state : InstructionContext.State.t StatefulHost.t WIRE WIRE_types)
      (frame : FrameInput.t) :
    finish checkpoint (Some (InterpreterAction.NewFrame frame, state)) =
    Some (InterpreterAction.NewFrame frame, state).
  Proof. reflexivity. Qed.
End StatefulFrame.
