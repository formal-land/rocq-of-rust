Require Import simulate.RocqOfRust.
Require Import revm.revm_context_interface.simulate.journaled_state.
Require Import revm.revm_interpreter.links.instruction_result.

Module Impl_InstructionResult.
  Definition is_ok (self : InstructionResult.t) : bool :=
    match self with
    | InstructionResult.Stop | InstructionResult.Return | InstructionResult.SelfDestruct => true
    | _ => false
    end.

  Definition is_revert (self : InstructionResult.t) : bool :=
    match self with
    | InstructionResult.Revert | InstructionResult.CallTooDeep | InstructionResult.OutOfFunds
    | InstructionResult.CreateInitCodeStartingEF00 | InstructionResult.InvalidEOFInitCode
    | InstructionResult.InvalidExtDelegateCallTarget => true
    | _ => false
    end.

  Definition is_ok_or_revert (self : InstructionResult.t) : bool := is_ok self || is_revert self.

  Definition from_transfer_error (error : TransferError.t) : InstructionResult.t :=
    match error with
    | TransferError.OutOfFunds => InstructionResult.OutOfFunds
    | TransferError.OverflowPayment => InstructionResult.OverflowPayment
    | TransferError.CreateCollision => InstructionResult.CreateCollision
    end.
End Impl_InstructionResult.
