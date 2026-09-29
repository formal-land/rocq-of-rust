From Stdlib Require Import List ZArith.

Require Import core.links.result.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.call_frame.
Require Import revm.revm_interpreter.tests.call_runner.
Require Import revm.revm_interpreter.tests.calls.
Require Import revm.revm_interpreter.tests.create.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_interpreter.tests.static_calls.
Require Import revm.revm_primitives.links.hardfork.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition account (address : Z)
      (result : option (InterpreterAction.t * CallFrame.state)) :=
    match result with
    | Some (_, state) => StatefulHost.find_account address
        (InstructionContext.State.host _ _ _ state).(StatefulHost.accounts)
    | None => None
    end.

  Lemma existing_contract_transfers_but_keeps_code :
    let result := calls.Test.run [96; 43; 255; 80] [] in
    (static_calls.Test.result_kind result, calls.Test.balance 42 result,
     calls.Test.balance 43 result, option_map StatefulHost.Account.code (account 42 result),
     calls.Test.remaining_gas result) =
    (Some InstructionResult.SelfDestruct, Some 0, Some 10,
     Some [96; 43; 255; 80], Some 67397).
  Proof. vm_compute. reflexivity. Qed.

  Lemma existing_self_beneficiary_keeps_balance :
    let result := calls.Test.run [48; 255; 80] [] in
    (static_calls.Test.result_kind result,
     calls.Test.balance 42 result, calls.Test.remaining_gas result) =
      (Some InstructionResult.SelfDestruct, Some 10, Some 94998).
  Proof. vm_compute. reflexivity. Qed.

  Lemma parent_revert_restores_child_transfer :
    let result := calls.Test.run
      (calls.Test.call 3 0 0 50000 ++ [96; 0; 96; 0; 253]) [96; 44; 255] in
    (calls.Test.balance 42 result, calls.Test.balance 43 result,
     calls.Test.balance 44 result) = (Some 10, Some 0, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_out_of_gas_restores_transfer :
    let result := calls.Test.run
      (calls.Test.call 3 0 0 10000 ++ [0]) [96; 45; 255] in
    (calls.Test.stack result, calls.Test.balance 42 result,
     calls.Test.balance 43 result, calls.Test.balance 45 result) =
      (Some [0], Some 10, Some 0, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma static_guard_precedes_underflow :
    static_calls.Test.result_kind (static_calls.Test.run_static [255] []) =
      Some InstructionResult.StateChangeDuringStaticCall.
  Proof. vm_compute. reflexivity. Qed.

  Lemma stack_underflow :
    static_calls.Test.result_kind (calls.Test.run [255] []) =
      Some InstructionResult.StackUnderflow.
  Proof. vm_compute. reflexivity. Qed.

  Definition host := InstructionContext.State.host _ _ _
    (calls.Test.initial [96; 43; 255] []).
  Definition destroy (host : StatefulHost.t) (target : Z) (skip : bool) :=
    StatefulHost.selfdestruct host (StatefulHost.rust_address 42)
      (StatefulHost.rust_address target) skip.

  Lemma skipped_cold_load_preserves_host :
    destroy host 43 true = (Result.Err LoadError.ColdLoadSkipped, host).
  Proof. vm_compute. reflexivity. Qed.

  Lemma beneficiary_warms_and_empty_account_is_not_existing :
    let '(result, after) := destroy host 43 false in
    match result with
    | Result.Ok load =>
        load.(StateLoad.is_cold) = true /\
        load.(StateLoad.data).(SelfDestructResult.target_exists) = false /\
        StatefulHost.account_is_warm after 43 = true
    | _ => False
    end.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Lemma created_contract_deletion_is_deferred :
    let created := StatefulHost.append_change host (StatefulHost.Change.Created 42) in
    let after := snd (destroy created 43 false) in
    option_map StatefulHost.Account.code
      (StatefulHost.find_account 42 after.(StatefulHost.accounts)) = Some [96; 43; 255] /\
    StatefulHost.find_account 42
      (StatefulHost.finalize_selfdestructs after).(StatefulHost.accounts) = None.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma created_self_beneficiary_burns_balance :
    let created := StatefulHost.append_change host (StatefulHost.Change.Created 42) in
    let after := snd (destroy created 42 false) in
    CallFrame.balance after 42 = 0 /\
    StatefulHost.was_selfdestructed 42 after.(StatefulHost.state_changes) = true.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma pre_cancun_existing_contract_is_marked :
    let after := snd (destroy (host <| StatefulHost.spec_id := SpecId.SHANGHAI |>) 42 false) in
    CallFrame.balance after 42 = 0 /\
    StatefulHost.was_selfdestructed 42 after.(StatefulHost.state_changes) = true.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma constructor_selfdestruct_removes_new_account :
    let init := [96; 44; 255] in
    let result := create.Test.run false init 3 [0] in
    account (create.Test.address false init) result = None /\
    calls.Test.balance 44 result = Some 3 /\
    create.Test.nonce 42 result = Some 8.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Lemma parent_revert_undoes_constructor_selfdestruct :
    let result := create.Test.run false [96; 44; 255] 3 [96; 0; 96; 0; 253] in
    calls.Test.balance 42 result = Some 100 /\
    calls.Test.balance 44 result = Some 0 /\
    create.Test.nonce 42 result = Some 7.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Definition deploy_selfdestruct :=
    create.Test.memory_code [96; 44; 255] ++ [96; 3; 96; 0; 243].

  Definition call_created (value : Z) :=
    [96; 0; 96; 0; 96; 0; 96; 0; 96; value;
     96; 32; 81; 97; 195; 80; 241].

  Definition repeat_created_selfdestruct (tail : list Z) :=
    create.Test.run false deploy_selfdestruct 3
      ([96; 32; 82] ++ call_created 0 ++
       [96; 32; 81; 59] ++ call_created 4 ++ tail).

  Lemma repeated_created_selfdestruct_executes_before_deletion :
    let result := repeat_created_selfdestruct [0] in
    static_calls.Test.result_kind result = Some InstructionResult.Stop /\
    calls.Test.stack result = Some [1; 3; 1] /\
    calls.Test.balance 42 result = Some 93 /\
    calls.Test.balance 44 result = Some 7 /\
    account (create.Test.address false deploy_selfdestruct) result = None.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Lemma parent_revert_undoes_repeated_created_selfdestruct :
    let result := repeat_created_selfdestruct [96; 0; 96; 0; 253] in
    static_calls.Test.result_kind result = Some InstructionResult.Revert /\
    calls.Test.stack result = Some [1; 3; 1] /\
    calls.Test.balance 42 result = Some 100 /\
    calls.Test.balance 44 result = Some 0 /\
    create.Test.nonce 42 result = Some 7 /\
    account (create.Test.address false deploy_selfdestruct) result = None.
  Proof. vm_compute. repeat split; reflexivity. Qed.
End Test.
