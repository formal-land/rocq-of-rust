From Stdlib Require Import List ZArith.

Require Import revm.revm_interpreter.interpreter.links.runtime_flags.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.call_context.
Require Import revm.revm_interpreter.tests.call_frame.
Require Import revm.revm_interpreter.tests.call_runner.
Require Import revm.revm_interpreter.tests.calls.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition static_call (address out_size : Z) : list Z :=
    [96; out_size; 96; 0; 96; 0; 96; 0; 96; address; 97; 195; 80; 250].

  Lemma empty_static_child_succeeds :
    calls.Test.stack (calls.Test.run (static_call 43 0 ++ [0]) []) = Some [1].
  Proof. vm_compute. reflexivity. Qed.

  Lemma static_child_cannot_store :
    calls.Test.stack (calls.Test.run (static_call 43 0 ++ [0])
      (calls.Test.write_seven ++ [0])) = Some [0].
  Proof. vm_compute. reflexivity. Qed.

  Lemma rejected_write_leaves_child_storage_unchanged :
    calls.Test.storage 43 (calls.Test.run (static_call 43 0 ++ [0])
      (calls.Test.write_seven ++ [0])) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma parent_remains_writable_after_static_failure :
    calls.Test.storage 42 (calls.Test.run
      (static_call 43 0 ++ [80] ++ calls.Test.write_seven ++ [0])
      (calls.Test.write_seven ++ [0])) = Some [(0, 7)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma static_child_can_return_memory :
    calls.Test.memory_prefix 1 (calls.Test.run (static_call 43 1 ++ [0])
      [96; 42; 96; 0; 83; 96; 1; 96; 0; 243]) = Some [42].
  Proof. vm_compute. reflexivity. Qed.

  Lemma static_child_can_read_storage :
    calls.Test.stack (calls.Test.run (static_call 43 0 ++ [0])
      [96; 0; 84; 80; 0]) = Some [1].
  Proof. vm_compute. reflexivity. Qed.

  Lemma static_child_cannot_call_with_value :
    calls.Test.stack (calls.Test.run (static_call 43 0 ++ [0])
      (calls.Test.call_to 44 1 0 0 30000 ++ [0])) = Some [0].
  Proof. vm_compute. reflexivity. Qed.

  Lemma nested_call_inherits_static_restriction :
    calls.Test.storage 44 (calls.Test.run (static_call 43 0 ++ [0])
      (calls.Test.call_to 44 0 0 0 30000 ++ [0])) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma nested_failure_does_not_fail_static_parent :
    calls.Test.stack (calls.Test.run (static_call 43 0 ++ [0])
      (calls.Test.call_to 44 0 0 0 30000 ++ [0])) = Some [1].
  Proof. vm_compute. reflexivity. Qed.

  Lemma static_precompile_remains_unsupported :
    calls.Test.run (static_call 1 0 ++ [0]) [] = None.
  Proof. vm_compute. reflexivity. Qed.

  Definition return_success_byte : list Z := [96; 0; 83; 96; 1; 96; 0; 243].

  Lemma static_then_callcode_rejects_grandchild_write :
    let result := calls.Test.run (static_call 43 1 ++ [0])
      ([96; 0; 96; 0; 96; 0; 96; 0; 96; 0; 96; 44; 97; 117; 48; 242]
        ++ return_success_byte) in
    (calls.Test.returned_bytes result, calls.Test.storage 43 result) =
      (Some [0], Some []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma static_then_delegatecall_rejects_grandchild_write :
    let result := calls.Test.run (static_call 43 1 ++ [0])
      ([96; 0; 96; 0; 96; 0; 96; 0; 96; 44; 97; 117; 48; 244]
        ++ return_success_byte) in
    (calls.Test.returned_bytes result, calls.Test.storage 43 result) =
      (Some [0], Some []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma static_child_value_is_zero_despite_parent_value :
    calls.Test.returned_bytes (CallRunner.run 200
      (call_context.Test.initial (static_call 43 1 ++ [0])
        ([52] ++ return_success_byte))) = Some [0].
  Proof. vm_compute. reflexivity. Qed.

  Definition run_static (parent child : list Z) :=
    let state := calls.Test.initial parent child in
    let interpreter := InstructionContext.State.interpreter _ _ _ state in
    CallRunner.run 200
      {| InstructionContext.State.interpreter := interpreter
           <| @Interpreter.runtime_flag WIRE _ WIRE_types _ :=
             interpreter.(Interpreter.runtime_flag) <| RuntimeFlags.is_static := true |> |>;
         InstructionContext.State.host := InstructionContext.State.host _ _ _ state |}.

  Definition result_kind (result : option (InterpreterAction.t * CallFrame.state)) :=
    match result with
    | Some (InterpreterAction.Return output, _) => Some output.(InterpreterResult.result)
    | _ => None
    end.

  Lemma storage_write_reports_static_violation :
    result_kind (run_static (calls.Test.write_seven ++ [0]) []) =
      Some InstructionResult.StateChangeDuringStaticCall.
  Proof. vm_compute. reflexivity. Qed.

  Lemma value_call_reports_static_violation_before_funds_check :
    result_kind (run_static (calls.Test.call 11 0 0 30000 ++ [0]) []) =
      Some InstructionResult.CallNotAllowedInsideStatic.
  Proof. vm_compute. reflexivity. Qed.

  Lemma funded_static_callcode_with_value_succeeds :
    calls.Test.stack (run_static (call_context.Test.call_code 3 ++ [0]) [0]) = Some [1].
  Proof. vm_compute. reflexivity. Qed.

  Lemma static_callcode_does_not_transfer_value :
    let result := run_static (call_context.Test.call_code 3 ++ [0]) [0] in
    (calls.Test.balance 42 result, calls.Test.balance 43 result) = (Some 10, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma static_callcode_still_checks_funds :
    calls.Test.stack (run_static (call_context.Test.call_code 11 ++ [0]) [0]) = Some [0].
  Proof. vm_compute. reflexivity. Qed.

  Lemma callcode_inherits_static_flag :
    let result := run_static (call_context.Test.call_code 0 ++ [0])
      (calls.Test.write_seven ++ [0]) in
    (calls.Test.stack result, calls.Test.storage 42 result) = (Some [0], Some []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegatecall_inherits_static_flag :
    let result := run_static (call_context.Test.delegate_call ++ [0])
      (calls.Test.write_seven ++ [0]) in
    (calls.Test.stack result, calls.Test.storage 42 result) = (Some [0], Some []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma static_success_returns_unused_gas :
    calls.Test.remaining_gas (calls.Test.run (static_call 43 0 ++ [0]) []) = Some 97382.
  Proof. vm_compute. reflexivity. Qed.

  Lemma static_violation_consumes_child_gas :
    calls.Test.remaining_gas (calls.Test.run (static_call 43 0 ++ [0])
      (calls.Test.write_seven ++ [0])) = Some 47382.
  Proof. vm_compute. reflexivity. Qed.

  Lemma static_revert_returns_data :
    let result := calls.Test.run (static_call 43 1 ++ [0])
      [96; 42; 96; 0; 83; 96; 1; 96; 0; 253] in
    (calls.Test.stack result, calls.Test.returned_bytes result) = (Some [0], Some [42]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma static_read_observes_nonzero_storage :
    let state := calls.Test.initial (static_call 43 1 ++ [0])
      [96; 0; 84; 96; 0; 83; 96; 1; 96; 0; 243] in
    let host := InstructionContext.State.host _ _ _ state in
    let host := StatefulHost.with_accounts host
      (StatefulHost.update_account 43
        (fun account => account <| StatefulHost.Account.storage := [(0, 42)] |>)
        host.(StatefulHost.accounts)) in
    calls.Test.memory_prefix 1 (CallRunner.run 200
      {| InstructionContext.State.interpreter := InstructionContext.State.interpreter _ _ _ state;
         InstructionContext.State.host := host |}) = Some [42].
  Proof. vm_compute. reflexivity. Qed.
End Test.
