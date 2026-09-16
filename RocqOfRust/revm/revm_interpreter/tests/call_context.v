From Stdlib Require Import List ZArith.

Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.call_frame.
Require Import revm.revm_interpreter.tests.call_runner.
Require Import revm.revm_interpreter.tests.calls.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition call_code (value : Z) : list Z :=
    [96; 0; 96; 0; 96; 0; 96; 0; 96; value; 96; 43; 98; 1; 17; 112; 242].

  Definition delegate_call : list Z :=
    [96; 0; 96; 0; 96; 0; 96; 0; 96; 43; 98; 1; 17; 112; 244].

  Definition initial (parent child : list Z) : CallFrame.state :=
    let state := calls.Test.initial parent child in
    let interpreter := InstructionContext.State.interpreter _ _ _ state in
    {| InstructionContext.State.interpreter := interpreter
         <| @Interpreter.input WIRE _ WIRE_types _ := interpreter.(Interpreter.input)
           <| Input.caller_address := StatefulHost.rust_address 77 |>
           <| Input.call_value := StatefulHost.rust_word 23 |> |>;
       InstructionContext.State.host := InstructionContext.State.host _ _ _ state |}.

  Definition run (parent child : list Z) := CallRunner.run 300 (initial parent child).

  Definition context_code : list Z :=
    [48; 96; 0; 85; 51; 96; 1; 85; 52; 96; 2; 85; 0].

  Definition slot (address key : Z) (result : option (InterpreterAction.t * CallFrame.state)) :=
    option_map (StatefulHost.lookup_word key) (calls.Test.storage address result).

  Lemma callcode_uses_parent_address :
    slot 42 0 (run (call_code 3 ++ [0]) context_code) = Some 42.
  Proof. vm_compute. reflexivity. Qed.

  Lemma callcode_caller_is_current_contract :
    slot 42 1 (run (call_code 3 ++ [0]) context_code) = Some 42.
  Proof. vm_compute. reflexivity. Qed.

  Lemma callcode_uses_explicit_value :
    slot 42 2 (run (call_code 3 ++ [0]) context_code) = Some 3.
  Proof. vm_compute. reflexivity. Qed.

  Lemma callcode_does_not_write_code_account :
    calls.Test.storage 43 (run (call_code 3 ++ [0]) context_code) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma callcode_keeps_parent_balance :
    calls.Test.balance 42 (run (call_code 3 ++ [0]) [0]) = Some 10.
  Proof. vm_compute. reflexivity. Qed.

  Lemma callcode_does_not_pay_code_account :
    calls.Test.balance 43 (run (call_code 3 ++ [0]) [0]) = Some 0.
  Proof. vm_compute. reflexivity. Qed.

  Lemma callcode_checks_funds_even_without_transfer :
    calls.Test.stack (run (call_code 11 ++ [0]) [0]) = Some [0].
  Proof. vm_compute. reflexivity. Qed.

  Lemma callcode_insufficient_funds_skips_child :
    calls.Test.storage 42 (run (call_code 11 ++ [0]) context_code) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegatecall_uses_parent_address :
    slot 42 0 (run (delegate_call ++ [0]) context_code) = Some 42.
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegatecall_preserves_original_caller :
    slot 42 1 (run (delegate_call ++ [0]) context_code) = Some 77.
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegatecall_keeps_apparent_value_above_balance :
    slot 42 2 (run (delegate_call ++ [0]) context_code) = Some 23.
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegatecall_does_not_write_code_account :
    calls.Test.storage 43 (run (delegate_call ++ [0]) context_code) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegatecall_does_not_debit_parent :
    calls.Test.balance 42 (run (delegate_call ++ [0]) context_code) = Some 10.
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegatecall_does_not_pay_code_account :
    calls.Test.balance 43 (run (delegate_call ++ [0]) context_code) = Some 0.
  Proof. vm_compute. reflexivity. Qed.

  Lemma callcode_revert_restores_parent_storage :
    calls.Test.storage 42 (run (call_code 0 ++ [0])
      (calls.Test.write_seven ++ [96; 0; 96; 0; 253])) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegatecall_revert_restores_parent_storage :
    calls.Test.storage 42 (run (delegate_call ++ [0])
      (calls.Test.write_seven ++ [96; 0; 96; 0; 253])) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegatecall_revert_preserves_earlier_parent_write :
    slot 42 0 (run (calls.Test.write_seven ++ delegate_call ++ [0])
      [96; 9; 96; 0; 85; 96; 0; 96; 0; 253]) = Some 7.
  Proof. vm_compute. reflexivity. Qed.

  Lemma callcode_revert_preserves_earlier_parent_write :
    slot 42 0 (run (calls.Test.write_seven ++ call_code 0 ++ [0])
      [96; 9; 96; 0; 85; 96; 0; 96; 0; 253]) = Some 7.
  Proof. vm_compute. reflexivity. Qed.

  Lemma parent_revert_undoes_successful_delegatecall :
    calls.Test.storage 42 (run (delegate_call ++ [96; 0; 96; 0; 253])
      (calls.Test.write_seven ++ [0])) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma parent_revert_undoes_successful_callcode :
    calls.Test.storage 42 (run (call_code 0 ++ [96; 0; 96; 0; 253])
      (calls.Test.write_seven ++ [0])) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegatecall_exception_restores_parent_storage :
    calls.Test.storage 42 (run (delegate_call ++ [0])
      (calls.Test.write_seven ++ [80])) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegatecall_rollback_undoes_grandchild_storage :
    calls.Test.storage 44 (run (delegate_call ++ [0])
      (calls.Test.call_to 44 0 0 0 30000 ++ [96; 0; 96; 0; 253])) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegatecall_rollback_restores_child_warmth :
    calls.Test.warm_accounts (run (delegate_call ++ [0])
      (calls.Test.call_to 44 0 0 0 30000 ++ [96; 0; 96; 0; 253])) = Some [43; 42].
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegatecall_returns_unused_child_gas :
    calls.Test.remaining_gas (run (delegate_call ++ [0]) [0]) = Some 97382.
  Proof. vm_compute. reflexivity. Qed.

  Lemma callcode_value_stipend_does_not_transfer_balance :
    calls.Test.remaining_gas (run (call_code 3 ++ [0]) [0]) = Some 90679.
  Proof. vm_compute. reflexivity. Qed.
End Test.
