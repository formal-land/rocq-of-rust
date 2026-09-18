From Stdlib Require Import List ZArith.

Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.simulate.dispatch.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.call_context.
Require Import revm.revm_interpreter.tests.calls.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.tests.stateful_dispatch.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_interpreter.tests.static_calls.
Require Import revm.revm_primitives.links.hardfork.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition write_seven : list Z := [96; 7; 96; 0; 93].
  Definition read_zero : list Z := [96; 0; 92].

  Definition fork_error (spec : SpecId.t) (opcode : Z) :=
    let state := calls.Test.initial [] [] in
    let state := {| InstructionContext.State.interpreter :=
      interpreter_with_spec_id (InstructionContext.State.interpreter _ _ _ state) spec;
      InstructionContext.State.host := InstructionContext.State.host _ _ _ state |} in
    let state := InterpreterDispatch.stateful
      (IInterpreterTypes := InterpreterTypes.I) (StatefulHost.rust_byte opcode) state in
    match (InstructionContext.State.interpreter _ _ _ state).(Interpreter.bytecode)
      .(Bytecode.action) with
    | Some (InterpreterAction.Return output) => Some output.(InterpreterResult.result)
    | _ => None
    end.

  Lemma both_operations_reject_before_cancun :
    (fork_error SpecId.SHANGHAI 92, fork_error SpecId.SHANGHAI 93) =
      (Some InstructionResult.NotActivated, Some InstructionResult.NotActivated).
  Proof. vm_compute. reflexivity. Qed.

  Lemma cancun_reaches_stack_validation :
    (fork_error SpecId.CANCUN 92, fork_error SpecId.CANCUN 93) =
      (Some InstructionResult.StackUnderflow, Some InstructionResult.StackUnderflow).
  Proof. vm_compute. reflexivity. Qed.

  Lemma prague_reaches_stack_validation :
    (fork_error SpecId.PRAGUE 92, fork_error SpecId.PRAGUE 93) =
      (Some InstructionResult.StackUnderflow, Some InstructionResult.StackUnderflow).
  Proof. vm_compute. reflexivity. Qed.

  Lemma unset_slot_is_zero :
    calls.Test.stack (calls.Test.run (read_zero ++ [0]) []) = Some [0].
  Proof. vm_compute. reflexivity. Qed.

  Lemma write_then_read :
    calls.Test.stack (calls.Test.run (write_seven ++ read_zero ++ [0]) []) = Some [7].
  Proof. vm_compute. reflexivity. Qed.

  Lemma both_operations_charge_one_hundred_gas :
    calls.Test.remaining_gas
      (calls.Test.run (write_seven ++ read_zero ++ [0]) []) = Some 99791.
  Proof. vm_compute. reflexivity. Qed.

  Lemma zero_overwrites_previous_value :
    calls.Test.stack (calls.Test.run
      (write_seven ++ [96; 0; 96; 0; 93] ++ read_zero ++ [0]) []) = Some [0].
  Proof. vm_compute. reflexivity. Qed.

  Lemma transient_write_does_not_change_persistent_storage :
    calls.Test.storage 42 (calls.Test.run (write_seven ++ [0]) []) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma call_has_separate_transient_storage :
    calls.Test.stack (calls.Test.run
      (write_seven ++ calls.Test.call 0 0 0 50000 ++ read_zero ++ [0])
      [96; 9; 96; 0; 93; 0]) = Some [7; 1].
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegatecall_shares_transient_storage :
    calls.Test.stack (calls.Test.run
      (call_context.Test.delegate_call ++ [80] ++ read_zero ++ [0])
      (write_seven ++ [0])) = Some [7].
  Proof. vm_compute. reflexivity. Qed.

  Lemma callcode_shares_transient_storage :
    calls.Test.stack (calls.Test.run
      (call_context.Test.call_code 0 ++ [80] ++ read_zero ++ [0])
      (write_seven ++ [0])) = Some [7].
  Proof. vm_compute. reflexivity. Qed.

  Lemma child_revert_restores_prior_transient_value :
    calls.Test.stack (calls.Test.run
      (write_seven ++ call_context.Test.delegate_call ++ read_zero ++ [0])
      [96; 9; 96; 0; 93; 96; 0; 96; 0; 253]) = Some [7; 0].
  Proof. vm_compute. reflexivity. Qed.

  Lemma staticcall_rejects_transient_write :
    calls.Test.stack (calls.Test.run (static_calls.Test.static_call 43 0 ++ [0])
      (write_seven ++ [0])) = Some [0].
  Proof. vm_compute. reflexivity. Qed.

  Lemma out_of_gas_restores_prior_transient_value :
    calls.Test.stack (calls.Test.run
      (write_seven ++
       [96; 0; 96; 0; 96; 0; 96; 0; 96; 43; 96; 110; 244] ++
       read_zero ++ [0])
      [96; 9; 96; 0; 93; 96; 0; 92; 0]) = Some [7; 0].
  Proof. vm_compute. reflexivity. Qed.

  Lemma static_write_reports_exact_error :
    static_calls.Test.result_kind (static_calls.Test.run_static (write_seven ++ [0]) []) =
      Some InstructionResult.StateChangeDuringStaticCall.
  Proof. vm_compute. reflexivity. Qed.

  Lemma staticcall_allows_transient_read :
    calls.Test.stack (calls.Test.run (static_calls.Test.static_call 43 0 ++ [0])
      (read_zero ++ [80; 0])) = Some [1].
  Proof. vm_compute. reflexivity. Qed.

  Lemma fresh_execution_starts_empty :
    calls.Test.stack (calls.Test.run (write_seven ++ read_zero ++ [0]) []) = Some [7] /\
    calls.Test.stack (calls.Test.run (read_zero ++ [0]) []) = Some [0].
  Proof. vm_compute. split; reflexivity. Qed.
End Test.
