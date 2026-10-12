From Stdlib Require Import List ZArith.

Require Import alloy_primitives.utils.simulate.keccak256.
Require Import revm.revm_handler.simulate.legacy_call.
Require Import revm.revm_handler.simulate.transaction_accounting.
Require Import revm.revm_interpreter.interpreter_action.links.create_inputs.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_InterpreterResult.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.call_frame.
Require Import revm.revm_interpreter.tests.create.
Require Import revm.revm_interpreter.tests.create_address.
Require Import revm.revm_interpreter.tests.create_frame.
Require Import revm.revm_interpreter.tests.precompile_frame.
Require Import revm.revm_interpreter.tests.stateful_dispatch.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_precompile.simulate.modexp.
Require Import revm.revm_precompile.simulate.kzg_point_evaluation.
Require Import revm.revm_primitives.links.hardfork.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition tx : TransactionAccounting.Transaction.t := {|
    TransactionAccounting.Transaction.tx_type := 0;
    TransactionAccounting.Transaction.caller := 100;
    TransactionAccounting.Transaction.target := Some 42;
    TransactionAccounting.Transaction.nonce := 0;
    TransactionAccounting.Transaction.chain_id := Some 1;
    TransactionAccounting.Transaction.gas_limit := 50000;
    TransactionAccounting.Transaction.gas_price := 10;
    TransactionAccounting.Transaction.max_priority_fee := None;
    TransactionAccounting.Transaction.access_list := [];
    TransactionAccounting.Transaction.max_fee_per_blob_gas := 0;
    TransactionAccounting.Transaction.blob_hashes := [];
    TransactionAccounting.Transaction.value := 7;
    TransactionAccounting.Transaction.data := [];
  |}.

  Definition input (code : list Z) : LegacyCall.Input.t := {|
    LegacyCall.Input.chain_id := 1;
    LegacyCall.Input.block := add11_input.(StatefulHost.Input.block)
      <| StatefulHost.Environment.Block.coinbase := 99 |>
      <| StatefulHost.Environment.Block.base_fee := 4 |>
      <| StatefulHost.Environment.Block.previous_randao := Some 0 |>;
    LegacyCall.Input.excess_blob_gas := Some 0;
    LegacyCall.Input.max_blobs_per_tx := None;
    LegacyCall.Input.accounts :=
      [(StatefulHost.empty_account 100) <| StatefulHost.Account.balance := 1000000 |>;
       (StatefulHost.empty_account 42) <| StatefulHost.Account.nonce := 1 |>
         <| StatefulHost.Account.code := code |>
         <| StatefulHost.Account.code_hash :=
           List.fold_left (fun value byte => 256 * value + byte)
             (Keccak256.hash code) 0 |>
         <| StatefulHost.Account.storage := [(0, 1)] |>;
       StatefulHost.empty_account 77];
  |}.

  Definition observation (result : LegacyCall.Result.t) :=
    match result with
    | LegacyCall.Result.Completed output =>
      let sender := LegacyCall.account_at 100 output.(LegacyCall.Output.accounts) in
      let target := LegacyCall.account_at 42 output.(LegacyCall.Output.accounts) in
      let coinbase := LegacyCall.account_at 99 output.(LegacyCall.Output.accounts) in
      Some (output.(LegacyCall.Output.status),
        output.(LegacyCall.Output.gas).(TransactionAccounting.Settlement.gas_used),
        sender.(StatefulHost.Account.nonce), sender.(StatefulHost.Account.balance),
        target.(StatefulHost.Account.balance), coinbase.(StatefulHost.Account.balance),
        StatefulHost.lookup_word 0 target.(StatefulHost.Account.storage))
    | _ => None
    end.

  Lemma stop_applies_value_nonce_and_exact_fees :
    observation (LegacyCall.run 100 SpecId.CANCUN tx (input [0])) =
    Some (InstructionResult.Stop, 21000, 1, 789993, 7, 126000, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma revert_restores_value_but_keeps_nonce_and_fees :
    observation (LegacyCall.run 100 SpecId.CANCUN tx (input [95; 95; 253])) =
    Some (InstructionResult.Revert, 21004, 1, 789960, 0, 126024, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma revert_restores_storage_and_discards_refund :
    observation (LegacyCall.run 100 SpecId.PRAGUE tx (input [95; 95; 85; 95; 95; 253])) =
    Some (InstructionResult.Revert, 26008, 1, 739920, 0, 156048, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma halt_rolls_back_value_and_spends_full_limit :
    observation (LegacyCall.run 100 SpecId.CANCUN tx (input [254])) =
    Some (InstructionResult.InvalidFEOpcode, 50000, 1, 500000, 0, 300000, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma successful_clear_settles_refund_and_removes_zero_slot :
    observation (LegacyCall.run 100 SpecId.CANCUN tx (input [95; 95; 85; 0])) =
    Some (InstructionResult.Stop, 21204, 1, 787953, 7, 127224, 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma prague_floor_applies_to_real_stop_execution :
    observation (LegacyCall.run 100 SpecId.PRAGUE
      (tx <| TransactionAccounting.Transaction.data := [1] |>) (input [0])) =
    Some (InstructionResult.Stop, 21040, 1, 789593, 7, 126240, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma nonce_rejection_is_distinct_from_execution_failure :
    LegacyCall.run 100 SpecId.CANCUN
      (tx <| TransactionAccounting.Transaction.nonce := 1 |>) (input [0]) =
    LegacyCall.Result.Rejected LegacyCall.Rejection.NonceTooHigh.
  Proof. vm_compute. reflexivity. Qed.

  Lemma code_rejection_precedes_payment_overflow :
    LegacyCall.run 100 SpecId.CANCUN
      (tx <| TransactionAccounting.Transaction.caller := 42 |>
          <| TransactionAccounting.Transaction.gas_price := 2 ^ 128 - 1 |>) (input [0]) =
    LegacyCall.Result.Rejected LegacyCall.Rejection.RejectCallerWithCode.
  Proof. vm_compute. reflexivity. Qed.

  Lemma insufficient_funds_is_transaction_rejection :
    LegacyCall.run 100 SpecId.CANCUN
      (tx <| TransactionAccounting.Transaction.value := 600000 |>) (input [0]) =
    LegacyCall.Result.Rejected LegacyCall.Rejection.LackOfFunds.
  Proof. vm_compute. reflexivity. Qed.

  Lemma pairing_out_of_gas_is_a_completed_transaction :
    match LegacyCall.run 100 SpecId.CANCUN
      (tx <| TransactionAccounting.Transaction.target := Some 8 |>) (input [0]) with
    | LegacyCall.Result.Completed output =>
        match output.(LegacyCall.Output.status) with
        | InstructionResult.PrecompileOOG => true
        | _ => false
        end
    | _ => false
    end = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma unreachable_nested_opcode_does_not_block_transaction :
    observation (LegacyCall.run 100 SpecId.PRAGUE tx (input [0; 241])) =
    Some (InstructionResult.Stop, 21000, 1, 789993, 7, 126000, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma pushed_call_byte_is_data :
    observation (LegacyCall.run 100 SpecId.PRAGUE tx (input [96; 241; 0])) =
    Some (InstructionResult.Stop, 21003, 1, 789963, 7, 126018, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma exhausted_runner_is_incomplete :
    LegacyCall.run O SpecId.CANCUN tx (input [0]) = LegacyCall.Result.Incomplete.
  Proof. vm_compute. reflexivity. Qed.

  Lemma self_call_does_not_transfer_value_twice :
    observation (LegacyCall.run 100 SpecId.CANCUN
      (tx <| TransactionAccounting.Transaction.target := Some 100 |>) (input [0])) =
    Some (InstructionResult.Stop, 21000, 1, 790000, 0, 126000, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma sender_as_coinbase_receives_its_reward :
    observation (LegacyCall.run 100 SpecId.CANCUN tx
      ((input [0]) <| LegacyCall.Input.block :=
        (input [0]).(LegacyCall.Input.block)
          <| StatefulHost.Environment.Block.coinbase := 100 |> |>)) =
    Some (InstructionResult.Stop, 21000, 1, 915993, 7, 0, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma target_as_coinbase_receives_value_and_reward :
    observation (LegacyCall.run 100 SpecId.CANCUN tx
      ((input [0]) <| LegacyCall.Input.block :=
        (input [0]).(LegacyCall.Input.block)
          <| StatefulHost.Environment.Block.coinbase := 42 |> |>)) =
    Some (InstructionResult.Stop, 21000, 1, 789993, 126007, 0, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma successful_zero_value_call_deletes_touched_empty_target :
    match LegacyCall.run 100 SpecId.CANCUN
      (tx <| TransactionAccounting.Transaction.value := 0 |>)
      ((input []) <| LegacyCall.Input.accounts :=
        [(StatefulHost.empty_account 100) <| StatefulHost.Account.balance := 1000000 |>;
         StatefulHost.empty_account 42; StatefulHost.empty_account 77] |>) with
    | LegacyCall.Result.Completed output =>
      StatefulHost.find_account 42 output.(LegacyCall.Output.accounts)
    | _ => None
    end = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma untouched_empty_account_is_preserved :
    match LegacyCall.run 100 SpecId.CANCUN tx (input [0]) with
    | LegacyCall.Result.Completed output =>
      StatefulHost.find_account 77 output.(LegacyCall.Output.accounts)
    | _ => None
    end = Some (StatefulHost.empty_account 77).
  Proof. vm_compute. reflexivity. Qed.

  Definition input_with_empty_beneficiary (code : list Z) (beneficiary : Z) :=
    let source := input code in
    source <| LegacyCall.Input.accounts := source.(LegacyCall.Input.accounts) ++
      [StatefulHost.empty_account beneficiary] |>.

  Definition beneficiary_observation (beneficiary : Z) (result : LegacyCall.Result.t) :=
    match result with
    | LegacyCall.Result.Completed output =>
      Some (output.(LegacyCall.Output.status),
        output.(LegacyCall.Output.gas).(TransactionAccounting.Settlement.gas_used),
        option_map StatefulHost.Account.balance
          (StatefulHost.find_account beneficiary output.(LegacyCall.Output.accounts)))
    | _ => None
    end.

  Lemma selfdestruct_dynamic_oog_keeps_ripemd_touch_and_reverts_value :
    let result := LegacyCall.run 100 SpecId.CANCUN tx
      (input_with_empty_beneficiary [96; 3; 255] 3) in
    (observation result, beneficiary_observation 3 result) =
    (Some (InstructionResult.OutOfGas, 50000, 1, 500000, 0, 300000, 1),
     Some (InstructionResult.OutOfGas, 50000, None)).
  Proof. vm_compute. reflexivity. Qed.

  Lemma selfdestruct_dynamic_oog_reverts_ordinary_beneficiary_touch :
    beneficiary_observation 88 (LegacyCall.run 100 SpecId.PRAGUE tx
      (input_with_empty_beneficiary [96; 88; 255] 88)) =
    Some (InstructionResult.OutOfGas, 50000, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma selfdestruct_static_oog_never_touches_ripemd :
    beneficiary_observation 3 (LegacyCall.run 100 SpecId.CANCUN
      (tx <| TransactionAccounting.Transaction.gas_limit := 25000 |>)
      (input_with_empty_beneficiary [96; 3; 255] 3)) =
    Some (InstructionResult.OutOfGas, 25000, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma successful_zero_balance_selfdestruct_deletes_empty_beneficiary :
    beneficiary_observation 3 (LegacyCall.run 100 SpecId.PRAGUE
      (tx <| TransactionAccounting.Transaction.value := 0 |>)
      (input_with_empty_beneficiary [96; 3; 255] 3)) =
    Some (InstructionResult.SelfDestruct, 26003, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma successful_selfdestruct_preserves_funded_beneficiary :
    beneficiary_observation 3 (LegacyCall.run 100 SpecId.CANCUN
      (tx <| TransactionAccounting.Transaction.gas_limit := 60000 |>)
      (input_with_empty_beneficiary [96; 3; 255] 3)) =
    Some (InstructionResult.SelfDestruct, 51003, Some 7).
  Proof. vm_compute. reflexivity. Qed.

  Lemma failed_selfdestruct_coinbase_alias_is_credited_before_cleanup :
    let source := input_with_empty_beneficiary [96; 3; 255] 3 in
    beneficiary_observation 3 (LegacyCall.run 100 SpecId.CANCUN tx
      (source <| LegacyCall.Input.block := source.(LegacyCall.Input.block)
        <| StatefulHost.Environment.Block.coinbase := 3 |> |>)) =
    Some (InstructionResult.OutOfGas, 50000, Some 300000).
  Proof. vm_compute. reflexivity. Qed.

  Lemma zero_reward_coinbase_is_touched_and_cleared :
    let source := input [0] in
    beneficiary_observation 99 (LegacyCall.run 100 SpecId.CANCUN
      (tx <| TransactionAccounting.Transaction.gas_price := 0 |>)
      (source <| LegacyCall.Input.block := source.(LegacyCall.Input.block)
        <| StatefulHost.Environment.Block.base_fee := 0 |> |>)) =
    Some (InstructionResult.Stop, 21000, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma ripemd_touch_survives_two_snapshot_rollbacks :
    let checkpoint := StatefulHost.make add11_input in
    let current := StatefulHost.touch_account
      (StatefulHost.touch_account checkpoint 88) 3 in
    StatefulHost.rollback checkpoint (StatefulHost.rollback checkpoint current) =
    StatefulHost.touch_account checkpoint 3.
  Proof. vm_compute. reflexivity. Qed.

  Lemma pre_spurious_rollback_restores_all_touches :
    let checkpoint := (StatefulHost.make add11_input)
      <| StatefulHost.spec_id := SpecId.HOMESTEAD |> in
    StatefulHost.rollback checkpoint (StatefulHost.touch_account checkpoint 3) = checkpoint.
  Proof. vm_compute. reflexivity. Qed.

  Definition nested_call (address value gas : Z) : list Z :=
    [96; 0; 96; 0; 96; 0; 96; 0; 96; value; 96; address;
     97; gas / 256; gas mod 256; 241].

  Definition nested_staticcall (address gas : Z) : list Z :=
    [96; 0; 96; 0; 96; 0; 96; 0; 96; address;
     97; gas / 256; gas mod 256; 250].

  Definition nested_delegatecall (address gas : Z) : list Z :=
    [96; 0; 96; 0; 96; 0; 96; 0; 96; address;
     97; gas / 256; gas mod 256; 244].

  Lemma zero_value_nested_call_clears_empty_callee :
    let result := LegacyCall.run 300 SpecId.CANCUN tx
      (input_with_empty_beneficiary (nested_call 88 0 10000 ++ [0]) 88) in
    (observation result, beneficiary_observation 88 result) =
    (Some (InstructionResult.Stop, 23621, 1, 763783, 7, 141726, 1),
     Some (InstructionResult.Stop, 23621, None)).
  Proof. vm_compute. reflexivity. Qed.

  Lemma zero_value_nested_staticcall_clears_empty_callee :
    beneficiary_observation 88 (LegacyCall.run 300 SpecId.PRAGUE tx
      (input_with_empty_beneficiary (nested_staticcall 88 10000 ++ [0]) 88)) =
    Some (InstructionResult.Stop, 23618, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegatecall_only_reads_empty_code_account :
    beneficiary_observation 88 (LegacyCall.run 300 SpecId.PRAGUE tx
      (input_with_empty_beneficiary (nested_delegatecall 88 10000 ++ [0]) 88)) =
    Some (InstructionResult.Stop, 23618, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma parent_revert_restores_ordinary_callee_touch :
    beneficiary_observation 88 (LegacyCall.run 300 SpecId.CANCUN tx
      (input_with_empty_beneficiary (nested_call 88 0 10000 ++ [95; 95; 253]) 88)) =
    Some (InstructionResult.Revert, 23625, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma failed_ripemd_call_retains_empty_account_touch :
    beneficiary_observation 3 (LegacyCall.run 300 SpecId.CANCUN tx
      (input_with_empty_beneficiary (nested_call 3 0 0 ++ [0]) 3)) =
    Some (InstructionResult.Stop, 21121, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma failed_sha256_call_reverts_empty_account_touch :
    beneficiary_observation 2 (LegacyCall.run 300 SpecId.CANCUN tx
      (input_with_empty_beneficiary (nested_call 2 0 0 ++ [0]) 2)) =
    Some (InstructionResult.Stop, 21121, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma failed_ripemd_staticcall_retains_empty_account_touch :
    beneficiary_observation 3 (LegacyCall.run 300 SpecId.PRAGUE tx
      (input_with_empty_beneficiary (nested_staticcall 3 0 ++ [0]) 3)) =
    Some (InstructionResult.Stop, 21118, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma parent_revert_preserves_failed_ripemd_touch :
    beneficiary_observation 3 (LegacyCall.run 300 SpecId.PRAGUE tx
      (input_with_empty_beneficiary (nested_call 3 0 0 ++ [95; 95; 253]) 3)) =
    Some (InstructionResult.Revert, 21125, None).
  Proof. vm_compute. reflexivity. Qed.

  Definition double_rollback_input :=
    let child := nested_call 3 0 0 ++ [95; 95; 253] in
    let source := input_with_empty_beneficiary
      (nested_call 43 0 10000 ++ [95; 95; 253]) 3 in
    source <| LegacyCall.Input.accounts := source.(LegacyCall.Input.accounts) ++
      [(StatefulHost.empty_account 43) <| StatefulHost.Account.nonce := 1 |>
        <| StatefulHost.Account.code := child |>
        <| StatefulHost.Account.code_hash :=
          List.fold_left (fun value byte => 256 * value + byte)
            (Keccak256.hash child) 0 |>] |>.

  Lemma two_ancestor_reverts_preserve_ripemd_touch :
    let result := LegacyCall.run 500 SpecId.CANCUN tx double_rollback_input in
    (observation result, beneficiary_observation 3 result) =
    (Some (InstructionResult.Revert, 23750, 1, 762500, 0, 142500, 1),
     Some (InstructionResult.Revert, 23750, None)).
  Proof. vm_compute. reflexivity. Qed.

  Definition creation_tx := tx <| TransactionAccounting.Transaction.gas_limit := 90000 |>.
  Definition created_address :=
    match CreateAddress.create 42 1 with Some address => address | None => 0 end.
  Definition created_account (result : LegacyCall.Result.t) :=
    match result with
    | LegacyCall.Result.Completed output =>
      option_map (fun account =>
        (account.(StatefulHost.Account.nonce), account.(StatefulHost.Account.balance),
         account.(StatefulHost.Account.code)))
        (StatefulHost.find_account created_address output.(LegacyCall.Output.accounts))
    | _ => None
    end.
  Definition target_nonce (result : LegacyCall.Result.t) :=
    match result with
    | LegacyCall.Result.Completed output =>
      option_map StatefulHost.Account.nonce
        (StatefulHost.find_account 42 output.(LegacyCall.Output.accounts))
    | _ => None
    end.

  Lemma nested_create_sets_nonces_value_code_and_transaction_fees :
    let result := LegacyCall.run 1000 SpecId.CANCUN creation_tx
      (input (create.Test.program false create.Test.deploy_stop 3 [0])) in
    (observation result, target_nonce result, created_account result) =
    (Some (InstructionResult.Stop, 53268, 1, 467313, 4, 319608, 1),
     Some 2, Some (1, 3, [0])).
  Proof. vm_compute. reflexivity. Qed.

  Lemma constructor_revert_keeps_creator_nonce_and_restores_value :
    let result := LegacyCall.run 1000 SpecId.PRAGUE creation_tx
      (input (create.Test.program false [95; 95; 253] 3 [0])) in
    (observation result, target_nonce result, created_account result) =
    (Some (InstructionResult.Stop, 53045, 1, 469543, 7, 318270, 1),
     Some 2, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma parent_revert_restores_creator_nonce_and_creation :
    let result := LegacyCall.run 1000 SpecId.CANCUN creation_tx
      (input (create.Test.program false create.Test.deploy_stop 3 [95; 95; 253])) in
    (observation result, target_nonce result, created_account result) =
    (Some (InstructionResult.Revert, 53272, 1, 467280, 0, 319632, 1),
     Some 1, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma constructor_selfdestruct_deletes_created_account_at_settlement :
    let result := LegacyCall.run 1000 SpecId.CANCUN creation_tx
      (input_with_empty_beneficiary (create.Test.program false [96; 88; 255] 3 [0]) 88) in
    (observation result, target_nonce result, created_account result,
     beneficiary_observation 88 result) =
    (Some (InstructionResult.Stop, 85644, 1, 143553, 4, 513864, 1),
     Some 2, None, Some (InstructionResult.Stop, 85644, Some 3)).
  Proof. vm_compute. reflexivity. Qed.

  Lemma destroyed_created_coinbase_is_finalized_after_fee_credit :
    let source := input_with_empty_beneficiary
      (create.Test.program false [96; 88; 255] 3 [0]) 88 in
    let source := source <| LegacyCall.Input.block := source.(LegacyCall.Input.block)
      <| StatefulHost.Environment.Block.coinbase := created_address |> |> in
    created_account (LegacyCall.run 1000 SpecId.PRAGUE creation_tx source) = None.
  Proof. vm_compute. reflexivity. Qed.

  Definition transfer_host := StatefulHost.make
    (add11_input <| StatefulHost.Input.state :=
      [(StatefulHost.empty_account 42) <| StatefulHost.Account.balance := 7 |>;
       StatefulHost.empty_account 88] |>).
  Definition transfer_observation (from to value : Z) :=
    let '(error, host) := CallFrame.transfer transfer_host from to value in
    (error, host.(StatefulHost.touched_accounts), CallFrame.balance host 42,
      CallFrame.balance host 88).

  Lemma same_address_transfer_does_not_touch :
    transfer_observation 42 42 7 = (None, [], 7, 0) /\
    transfer_observation 42 42 8 = (Some InstructionResult.OutOfFunds, [], 7, 0).
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma zero_transfer_touches_only_destination :
    transfer_observation 42 88 0 = (None, [88], 7, 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma nonzero_transfer_touches_source_and_destination :
    transfer_observation 42 88 3 = (None, [88; 42], 4, 3).
  Proof. vm_compute. reflexivity. Qed.

  Lemma insufficient_funds_touches_source_before_failure :
    transfer_observation 42 88 8 = (Some InstructionResult.OutOfFunds, [42], 7, 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma nonce_overflow_creation_still_touches_creator :
    let state := create.Test.initial [] in
    let host := InstructionContext.State.host _ _ _ state in
    let host := StatefulHost.with_accounts host
      (StatefulHost.update_account 42 (fun account => CreateFrame.with_nonce account (2 ^ 64 - 1))
        host.(StatefulHost.accounts)) in
    match CreateFrame.prepare (InstructionContext.State.interpreter _ _ _ state) host 1
      create.Test.inputs with
    | Some (CreateFrame.Immediate output host) =>
      (output.(InterpreterResult.result), host.(StatefulHost.touched_accounts))
    | _ => (InstructionResult.Continue, [])
    end = (InstructionResult.Return, [42]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma top_level_transfer_overflow_is_incomplete :
    let source := input [0] in
    let source := source <| LegacyCall.Input.accounts :=
      StatefulHost.update_account 42
        (fun account => StatefulHost.account_with_balance account (2 ^ 256 - 1))
        source.(LegacyCall.Input.accounts) |> in
    LegacyCall.run 300 SpecId.CANCUN tx source = LegacyCall.Result.Incomplete.
  Proof. vm_compute. reflexivity. Qed.

  Lemma nested_transfer_overflow_is_incomplete :
    let source := input (nested_call 88 1 10000 ++ [0]) in
    let source := source <| LegacyCall.Input.accounts := source.(LegacyCall.Input.accounts) ++
      [(StatefulHost.empty_account 88) <| StatefulHost.Account.balance := 2 ^ 256 - 1 |>] |> in
    LegacyCall.run 300 SpecId.PRAGUE tx source = LegacyCall.Result.Incomplete.
  Proof. vm_compute. reflexivity. Qed.

  Definition precompile_tx (address : Z) (data : list Z) := tx
    <| TransactionAccounting.Transaction.target := Some address |>
    <| TransactionAccounting.Transaction.data := data |>.

  Definition precompile_input (address : Z) (code : list Z) :=
    let source := input [] in
    source <| LegacyCall.Input.accounts := source.(LegacyCall.Input.accounts) ++
      [(StatefulHost.empty_account address)
        <| StatefulHost.Account.code := code |>
        <| StatefulHost.Account.code_hash :=
          List.fold_left (fun value byte => 256 * value + byte)
            (Keccak256.hash code) 0 |>] |>.

  Definition precompile_observation (address : Z) (result : LegacyCall.Result.t) :=
    match result with
    | LegacyCall.Result.Completed output =>
      let sender := LegacyCall.account_at 100 output.(LegacyCall.Output.accounts) in
      let target := LegacyCall.account_at address output.(LegacyCall.Output.accounts) in
      let coinbase := LegacyCall.account_at 99 output.(LegacyCall.Output.accounts) in
      Some (output.(LegacyCall.Output.status),
        output.(LegacyCall.Output.gas).(TransactionAccounting.Settlement.gas_used),
        sender.(StatefulHost.Account.nonce), sender.(StatefulHost.Account.balance),
        target.(StatefulHost.Account.balance), coinbase.(StatefulHost.Account.balance),
        output.(LegacyCall.Output.data))
    | _ => None
    end.

  Lemma top_level_identity_applies_value_nonce_and_exact_fees :
    precompile_observation 4 (LegacyCall.run 100 SpecId.CANCUN
      (precompile_tx 4 [1; 2; 3]) (precompile_input 4 [])) =
    Some (InstructionResult.Return, 21066, 1, 789333, 7, 126396, [1; 2; 3]).
  Proof. vm_compute. reflexivity. Qed.

  (* Digests independently calculated over the three bytes 0x01, 0x02, 0x03. *)
  Lemma top_level_sha256_applies_value_nonce_and_exact_fees :
    precompile_observation 2 (LegacyCall.run 100 SpecId.PRAGUE
      (precompile_tx 2 [1; 2; 3]) (precompile_input 2 [])) =
    Some (InstructionResult.Return, 21120, 1, 788793, 7, 126720,
      [3; 144; 88; 198; 242; 192; 203; 73; 44; 83; 59; 10; 77; 20; 239; 119;
       204; 15; 120; 171; 204; 206; 213; 40; 125; 132; 161; 162; 1; 28; 251; 129]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma top_level_ripemd160_applies_value_nonce_and_exact_fees :
    precompile_observation 3 (LegacyCall.run 100 SpecId.PRAGUE
      (precompile_tx 3 [1; 2; 3]) (precompile_input 3 [])) =
    Some (InstructionResult.Return, 21768, 1, 782313, 7, 130608,
      [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
       121; 249; 1; 218; 38; 9; 240; 32; 173; 173; 191; 46; 95; 104; 161; 108;
       140; 63; 125; 87]).
  Proof. vm_compute. reflexivity. Qed.

  Definition modexp_data : list Z :=
    Modexp.encode_be 32 1 ++ Modexp.encode_be 32 1 ++ Modexp.encode_be 32 1 ++ [3; 4; 5].

  Lemma top_level_modexp_applies_value_nonce_and_exact_fees :
    precompile_observation 5 (LegacyCall.run 100 SpecId.CANCUN
      (precompile_tx 5 modexp_data) (precompile_input 5 [])) =
    Some (InstructionResult.Return, 21668, 1, 783313, 7, 130008, [1]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma prague_floor_settles_top_level_precompile :
    precompile_observation 4 (LegacyCall.run 100 SpecId.PRAGUE
      (precompile_tx 4 [1; 2; 3]) (precompile_input 4 [])) =
    Some (InstructionResult.Return, 21120, 1, 788793, 7, 126720, [1; 2; 3]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma top_level_precompile_precedes_invalid_account_code :
    precompile_observation 4 (LegacyCall.run 100 SpecId.CANCUN
      (precompile_tx 4 [1; 2; 3]) (precompile_input 4 [254])) =
    Some (InstructionResult.Return, 21066, 1, 789333, 7, 126396, [1; 2; 3]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma top_level_precompile_precedes_delegation_account_code :
    precompile_observation 4 (LegacyCall.run 100 SpecId.PRAGUE
      (precompile_tx 4 [1; 2; 3]) (precompile_input 4 ([239; 1; 0] ++ List.repeat 0 20))) =
    Some (InstructionResult.Return, 21120, 1, 788793, 7, 126720, [1; 2; 3]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma top_level_identity_oog_rolls_back_value_and_burns_full_limit :
    precompile_observation 4 (LegacyCall.run 100 SpecId.CANCUN
      ((precompile_tx 4 [1; 2; 3]) <| TransactionAccounting.Transaction.gas_limit := 21065 |>)
      (precompile_input 4 [])) =
    Some (InstructionResult.PrecompileOOG, 21065, 1, 789350, 0, 126390, []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma top_level_sha256_oog_restores_ordinary_empty_account_touch :
    let result := LegacyCall.run 100 SpecId.CANCUN
      ((precompile_tx 2 []) <| TransactionAccounting.Transaction.gas_limit := 21059 |>)
      (precompile_input 2 []) in
    (precompile_observation 2 result, beneficiary_observation 2 result) =
    (Some (InstructionResult.PrecompileOOG, 21059, 1, 789410, 0, 126354, []),
     Some (InstructionResult.PrecompileOOG, 21059, Some 0)).
  Proof. vm_compute. reflexivity. Qed.

  Lemma top_level_ripemd160_oog_preserves_sticky_touch_for_cleanup :
    let result := LegacyCall.run 100 SpecId.PRAGUE
      ((precompile_tx 3 []) <| TransactionAccounting.Transaction.gas_limit := 21599 |>)
      (precompile_input 3 []) in
    (precompile_observation 3 result, beneficiary_observation 3 result) =
    (Some (InstructionResult.PrecompileOOG, 21599, 1, 784010, 0, 129594, []),
     Some (InstructionResult.PrecompileOOG, 21599, None)).
  Proof. vm_compute. reflexivity. Qed.

  Lemma top_level_modexp_oog_rolls_back_value_and_burns_full_limit :
    precompile_observation 5 (LegacyCall.run 100 SpecId.CANCUN
      ((precompile_tx 5 []) <| TransactionAccounting.Transaction.gas_limit := 21199 |>)
      (precompile_input 5 [])) =
    Some (InstructionResult.PrecompileOOG, 21199, 1, 788010, 0, 127194, []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma top_level_modexp_length_error_is_completed_exceptional_halt :
    let data := Modexp.encode_be 32 (2 ^ 64) ++ List.repeat 0 64 in
    precompile_observation 5 (LegacyCall.run 100 SpecId.PRAGUE
      (precompile_tx 5 data) (precompile_input 5 [])) =
    Some (InstructionResult.PrecompileError, 50000, 1, 500000, 0, 300000, []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma top_level_kzg_insufficient_gas_is_exceptional_halt :
    precompile_observation 10 (LegacyCall.run 100 SpecId.PRAGUE
      (precompile_tx 10 []) (precompile_input 10 [])) =
    Some (InstructionResult.PrecompileOOG, 50000, 1, 500000, 0, 300000, []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma unimplemented_kzg_proof_stays_incomplete :
    let invalid_point := List.repeat 0 48 in
    let data := KzgPointEvaluation.versioned_hash invalid_point ++
      List.repeat 0 64 ++ invalid_point ++ invalid_point in
    LegacyCall.run 100 SpecId.CANCUN
      ((precompile_tx 10 data) <| TransactionAccounting.Transaction.gas_limit := 75000 |>)
      (precompile_input 10 []) = LegacyCall.Result.Incomplete.
  Proof. vm_compute. reflexivity. Qed.

  Lemma other_top_level_precompiles_remain_explicitly_unsupported :
    LegacyCall.run 100 SpecId.PRAGUE (precompile_tx 17 []) (precompile_input 17 []) =
    LegacyCall.Result.Unsupported LegacyCall.Gap.TopLevelPrecompile.
  Proof. vm_compute. reflexivity. Qed.

  Lemma osaka_clz_executes_and_settles_exact_fees :
    observation (LegacyCall.run 100 SpecId.OSAKA tx (input [95; 30; 95; 85; 0])) =
    Some (InstructionResult.Stop, 26009, 1, 739903, 7, 156054, 256).
  Proof. vm_compute. reflexivity. Qed.

  Lemma osaka_top_level_modexp_keeps_prague_floor :
    precompile_observation 5 (LegacyCall.run 100 SpecId.OSAKA
      (precompile_tx 5 modexp_data) (precompile_input 5 [])) =
    Some (InstructionResult.Return, 22170, 1, 778293, 7, 133020, [1]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma osaka_warms_existing_bls_precompiles :
    observation (LegacyCall.run 100 SpecId.OSAKA tx (input [96; 11; 49; 0])) =
    Some (InstructionResult.Stop, 21103, 1, 788963, 7, 126618, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma osaka_warms_p256_without_touching_it :
    let result := LegacyCall.run 100 SpecId.OSAKA tx
      (input_with_empty_beneficiary [97; 1; 0; 49; 0] 256) in
    (observation result, beneficiary_observation 256 result) =
    (Some (InstructionResult.Stop, 21103, 1, 788963, 7, 126618, 1),
     Some (InstructionResult.Stop, 21103, Some 0)).
  Proof. vm_compute. reflexivity. Qed.

  Lemma prague_does_not_warm_p256 :
    observation (LegacyCall.run 100 SpecId.PRAGUE tx (input [97; 1; 0; 49; 0])) =
    Some (InstructionResult.Stop, 23603, 1, 763963, 7, 141618, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma osaka_p256_overrides_ordinary_bytecode_but_is_unsupported :
    LegacyCall.run 100 SpecId.OSAKA (precompile_tx 256 []) (precompile_input 256 [254]) =
    LegacyCall.Result.Unsupported LegacyCall.Gap.TopLevelPrecompile.
  Proof. vm_compute. reflexivity. Qed.

  Lemma prague_p256_address_executes_ordinary_bytecode :
    precompile_observation 256 (LegacyCall.run 100 SpecId.PRAGUE
      (precompile_tx 256 []) (precompile_input 256 [254])) =
    Some (InstructionResult.InvalidFEOpcode, 50000, 1, 500000, 0, 300000, []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma osaka_keeps_unimplemented_bls_precompile_explicit :
    LegacyCall.run 100 SpecId.OSAKA (precompile_tx 11 []) (input []) =
    LegacyCall.Result.Unsupported LegacyCall.Gap.TopLevelPrecompile.
  Proof. vm_compute. reflexivity. Qed.

  Lemma osaka_nested_p256_is_incomplete :
    LegacyCall.run 300 SpecId.OSAKA tx (input [95; 95; 95; 95; 95; 97; 1; 0;
      97; 195; 80; 241; 0]) = LegacyCall.Result.Incomplete.
  Proof. vm_compute. reflexivity. Qed.

  Lemma osaka_nested_create_keeps_existing_limits_and_deposit_fees :
    let result := LegacyCall.run 1000 SpecId.OSAKA creation_tx
      (input (create.Test.program false create.Test.deploy_stop 3 [0])) in
    (observation result, target_nonce result, created_account result) =
    (Some (InstructionResult.Stop, 53268, 1, 467313, 4, 319608, 1),
     Some 2, Some (1, 3, [0])).
  Proof. vm_compute. reflexivity. Qed.

  Lemma osaka_transaction_gas_cap_is_checked_before_price :
    LegacyCall.run 100 SpecId.OSAKA
      (tx <| TransactionAccounting.Transaction.gas_limit := 16777217 |>
          <| TransactionAccounting.Transaction.gas_price := 0 |>) (input [0]) =
    LegacyCall.Result.Rejected (LegacyCall.Rejection.Gas
      (TransactionAccounting.GasError.GasLimitAboveCap 16777217 16777216)).
  Proof. vm_compute. reflexivity. Qed.

  Lemma osaka_transaction_accepts_exact_gas_cap :
    let source := input [0] in
    observation (LegacyCall.run 100 SpecId.OSAKA
      (tx <| TransactionAccounting.Transaction.gas_limit := 16777216 |>
          <| TransactionAccounting.Transaction.gas_price := 0 |>)
      (source <| LegacyCall.Input.block := source.(LegacyCall.Input.block)
        <| StatefulHost.Environment.Block.gas_limit := 20000000 |>
        <| StatefulHost.Environment.Block.base_fee := 0 |> |>)) =
    Some (InstructionResult.Stop, 21000, 1, 999993, 7, 0, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma supported_fork_precompile_sets_are_exact :
    (List.map (PrecompileFrame.is_precompile SpecId.OSAKA) [0; 1; 17; 18; 255; 256; 257],
     List.map (fun spec => PrecompileFrame.is_precompile spec 256)
       [SpecId.CANCUN; SpecId.PRAGUE; SpecId.OSAKA]) =
    ([false; true; true; false; false; true; false], [false; false; true]).
  Proof. vm_compute. reflexivity. Qed.

  Definition access_list_tx (entries : list (Z * list Z)) :=
    tx <| TransactionAccounting.Transaction.tx_type := 1 |>
       <| TransactionAccounting.Transaction.access_list := entries |>.

  Definition dynamic_fee_tx :=
    tx <| TransactionAccounting.Transaction.tx_type := 2 |>
       <| TransactionAccounting.Transaction.max_priority_fee := Some 2 |>.

  Lemma access_list_stop_preserves_fee_value_and_nonce_accounting :
    observation (LegacyCall.run 100 SpecId.CANCUN
      (access_list_tx [(42, [0])]) (input [0])) =
    Some (InstructionResult.Stop, 25300, 1, 746993, 7, 151800, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma access_list_warms_storage_before_first_sload :
    observation (LegacyCall.run 100 SpecId.CANCUN
      (access_list_tx [(42, [0])]) (input [95; 84; 80; 0])) =
    Some (InstructionResult.Stop, 25404, 1, 745953, 7, 152424, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma duplicate_access_entries_pay_intrinsic_without_rewarming_storage :
    observation (LegacyCall.run 100 SpecId.CANCUN
      (access_list_tx [(42, [0; 0]); (42, [0])]) (input [95; 84; 80; 0])) =
    Some (InstructionResult.Stop, 31604, 1, 683953, 7, 189624, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma access_list_warms_other_account_before_balance :
    observation (LegacyCall.run 100 SpecId.PRAGUE
      (access_list_tx [(77, [])]) (input [96; 77; 49; 80; 0])) =
    Some (InstructionResult.Stop, 23505, 1, 764943, 7, 141030, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma warming_empty_account_does_not_delete_it :
    match LegacyCall.run 100 SpecId.CANCUN
      (access_list_tx [(77, [])]) (input [0]) with
    | LegacyCall.Result.Completed output =>
      StatefulHost.find_account 77 output.(LegacyCall.Output.accounts)
    | _ => None
    end = Some (StatefulHost.empty_account 77).
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_fee_stop_charges_effective_price_and_preserves_value_nonce :
    observation (LegacyCall.run 100 SpecId.CANCUN dynamic_fee_tx (input [0])) =
    Some (InstructionResult.Stop, 21000, 1, 873993, 7, 42000, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_fee_gasprice_opcode_observes_effective_price :
    observation (LegacyCall.run 100 SpecId.CANCUN dynamic_fee_tx (input [58; 95; 85; 0])) =
    Some (InstructionResult.Stop, 26004, 1, 843969, 7, 52008, 6).
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_fee_access_list_warms_storage :
    observation (LegacyCall.run 100 SpecId.OSAKA
      (dynamic_fee_tx <| TransactionAccounting.Transaction.access_list := [(42, [0])] |>)
      (input [95; 84; 80; 0])) =
    Some (InstructionResult.Stop, 25404, 1, 847569, 7, 50808, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_fee_revert_restores_value_but_charges_effective_fee :
    observation (LegacyCall.run 100 SpecId.PRAGUE dynamic_fee_tx (input [95; 95; 253])) =
    Some (InstructionResult.Revert, 21004, 1, 873976, 0, 42008, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_fee_halt_spends_limit_at_effective_price :
    observation (LegacyCall.run 100 SpecId.OSAKA dynamic_fee_tx (input [254])) =
    Some (InstructionResult.InvalidFEOpcode, 50000, 1, 700000, 0, 100000, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_fee_maximum_price_controls_affordability :
    LegacyCall.run 100 SpecId.CANCUN
      (dynamic_fee_tx <| TransactionAccounting.Transaction.gas_price := 30 |>) (input [0]) =
    LegacyCall.Result.Rejected LegacyCall.Rejection.LackOfFunds.
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_fee_maximum_payment_overflow_is_rejected :
    LegacyCall.run 100 SpecId.CANCUN
      (dynamic_fee_tx <| TransactionAccounting.Transaction.gas_price := 2 ^ 128 - 1 |>)
      (input [0]) =
    LegacyCall.Result.Rejected (LegacyCall.Rejection.Gas TransactionAccounting.GasError.PaymentOverflow).
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_fee_nonce_validation_precedes_payment :
    LegacyCall.run 100 SpecId.CANCUN
      (dynamic_fee_tx <| TransactionAccounting.Transaction.gas_price := 2 ^ 128 - 1 |>
        <| TransactionAccounting.Transaction.nonce := 1 |>) (input [0]) =
    LegacyCall.Result.Rejected LegacyCall.Rejection.NonceTooHigh.
  Proof. vm_compute. reflexivity. Qed.

  Lemma access_list_transaction_requires_chain_id :
    LegacyCall.run 100 SpecId.CANCUN
      ((access_list_tx []) <| TransactionAccounting.Transaction.chain_id := None |>) (input [0]) =
    LegacyCall.Result.Rejected LegacyCall.Rejection.MissingChainId.
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_fee_missing_chain_id_precedes_fee_validation :
    LegacyCall.run 100 SpecId.CANCUN
      (dynamic_fee_tx <| TransactionAccounting.Transaction.chain_id := None |>
        <| TransactionAccounting.Transaction.max_priority_fee := Some 11 |>) (input [0]) =
    LegacyCall.Result.Rejected LegacyCall.Rejection.MissingChainId.
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_fee_wrong_chain_id_is_rejected :
    LegacyCall.run 100 SpecId.CANCUN
      (dynamic_fee_tx <| TransactionAccounting.Transaction.chain_id := Some 2 |>) (input [0]) =
    LegacyCall.Result.Rejected LegacyCall.Rejection.InvalidChainId.
  Proof. vm_compute. reflexivity. Qed.

  Lemma legacy_transaction_may_omit_chain_id :
    observation (LegacyCall.run 100 SpecId.CANCUN
      (tx <| TransactionAccounting.Transaction.chain_id := None |>) (input [0])) =
    Some (InstructionResult.Stop, 21000, 1, 789993, 7, 126000, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_priority_above_max_fee_is_rejected_before_base_fee :
    LegacyCall.run 100 SpecId.CANCUN
      (dynamic_fee_tx <| TransactionAccounting.Transaction.gas_price := 3 |>
        <| TransactionAccounting.Transaction.max_priority_fee := Some 5 |>) (input [0]) =
    LegacyCall.Result.Rejected
      (LegacyCall.Rejection.Gas TransactionAccounting.GasError.PriorityFeeGreaterThanMaxFee).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_transaction_without_hashes_is_rejected :
    LegacyCall.run 100 SpecId.CANCUN
      (tx <| TransactionAccounting.Transaction.tx_type := 3 |>) (input [0]) =
    LegacyCall.Result.Rejected (LegacyCall.Rejection.Gas TransactionAccounting.GasError.EmptyBlobs).
  Proof. vm_compute. reflexivity. Qed.

  Lemma authorization_transaction_remains_unsupported :
    LegacyCall.run 100 SpecId.PRAGUE
      (tx <| TransactionAccounting.Transaction.tx_type := 4 |>) (input [0]) =
    LegacyCall.Result.Unsupported
      (LegacyCall.Gap.Accounting (TransactionAccounting.UnsupportedReason.TransactionType 4)).
  Proof. vm_compute. reflexivity. Qed.
  Definition input_with_max_nonce (code : list Z) :=
    let source := input code in
    source <| LegacyCall.Input.accounts :=
      StatefulHost.update_account 100 (fun account =>
        account <| StatefulHost.Account.nonce := 2 ^ 64 - 1 |>)
        source.(LegacyCall.Input.accounts) |>.

  Lemma native_call_max_nonce_keeps_nonce_and_executes :
    observation (LegacyCall.run 100 SpecId.CANCUN
      (tx <| TransactionAccounting.Transaction.nonce := 2 ^ 64 - 1 |>)
      (input_with_max_nonce [0])) =
    Some (InstructionResult.Stop, 21000, 2 ^ 64 - 1, 789993, 7, 126000, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma native_call_max_nonce_revert_keeps_nonce_and_fees :
    observation (LegacyCall.run 100 SpecId.CANCUN
      (tx <| TransactionAccounting.Transaction.nonce := 2 ^ 64 - 1 |>)
      (input_with_max_nonce [95; 95; 253])) =
    Some (InstructionResult.Revert, 21004, 2 ^ 64 - 1, 789960, 0, 126024, 1).
  Proof. vm_compute. reflexivity. Qed.


  Definition blob_hash : Z := 2 ^ 248 + 17.

  Definition blob_tx := dynamic_fee_tx
    <| TransactionAccounting.Transaction.tx_type := 3 |>
    <| TransactionAccounting.Transaction.max_fee_per_blob_gas := 3 |>
    <| TransactionAccounting.Transaction.blob_hashes := [blob_hash] |>.

  Definition blob_input (code : list Z) :=
    let source := input code in
    source <| LegacyCall.Input.block := source.(LegacyCall.Input.block)
      <| StatefulHost.Environment.Block.blob_base_fee := 2 |> |>.

  Lemma blob_stop_applies_effective_fees_value_and_nonce :
    observation (LegacyCall.run 100 SpecId.CANCUN blob_tx (blob_input [0])) =
    Some (InstructionResult.Stop, 21000, 1, 611849, 7, 42000, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_duplicate_hashes_each_charge_blob_fee :
    let source := blob_input [0] in
    let source := source <| LegacyCall.Input.accounts :=
      StatefulHost.update_account 100 (fun account =>
        account <| StatefulHost.Account.balance := 2000000 |>) source.(LegacyCall.Input.accounts) |> in
    observation (LegacyCall.run 100 SpecId.PRAGUE
      (blob_tx <| TransactionAccounting.Transaction.blob_hashes := [blob_hash; blob_hash] |>) source) =
    Some (InstructionResult.Stop, 21000, 1, 1349705, 7, 42000, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_revert_keeps_blob_fee_and_execution_fee :
    observation (LegacyCall.run 100 SpecId.PRAGUE blob_tx (blob_input [95; 95; 253])) =
    Some (InstructionResult.Revert, 21004, 1, 611832, 0, 42008, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_halt_keeps_blob_fee_and_spends_execution_limit :
    observation (LegacyCall.run 100 SpecId.OSAKA blob_tx (blob_input [254])) =
    Some (InstructionResult.InvalidFEOpcode, 50000, 1, 437856, 0, 100000, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blobhash_opcode_reads_original_versioned_hash :
    observation (LegacyCall.run 100 SpecId.CANCUN blob_tx (blob_input [95; 73; 95; 85; 0])) =
    Some (InstructionResult.Stop, 26007, 1, 581807, 7, 52014, blob_hash).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blobhash_out_of_range_returns_zero :
    observation (LegacyCall.run 100 SpecId.CANCUN blob_tx (blob_input [96; 1; 73; 95; 85; 0])) =
    Some (InstructionResult.Stop, 21208, 1, 610601, 7, 42416, 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blobhash_large_index_saturates_and_returns_zero :
    observation (LegacyCall.run 100 SpecId.CANCUN blob_tx
      (blob_input ([127] ++ List.repeat 255 32 ++ [73; 95; 85; 0]))) =
    Some (InstructionResult.Stop, 21208, 1, 610601, 7, 42416, 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blobbasefee_opcode_reads_header_price_used_for_deduction :
    observation (LegacyCall.run 100 SpecId.CANCUN blob_tx (blob_input [74; 95; 85; 0])) =
    Some (InstructionResult.Stop, 26004, 1, 581825, 7, 52008, 2).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_gasprice_opcode_reads_effective_execution_price :
    observation (LegacyCall.run 100 SpecId.CANCUN blob_tx (blob_input [58; 95; 85; 0])) =
    Some (InstructionResult.Stop, 26004, 1, 581825, 7, 52008, 6).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_affordability_uses_maximum_blob_price :
    LegacyCall.run 100 SpecId.CANCUN
      (blob_tx <| TransactionAccounting.Transaction.max_fee_per_blob_gas := 4 |>) (blob_input [0]) =
    LegacyCall.Result.Rejected LegacyCall.Rejection.LackOfFunds.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_nonce_validation_precedes_affordability :
    LegacyCall.run 100 SpecId.CANCUN
      (blob_tx <| TransactionAccounting.Transaction.max_fee_per_blob_gas := 4 |>
        <| TransactionAccounting.Transaction.nonce := 1 |>) (blob_input [0]) =
    LegacyCall.Result.Rejected LegacyCall.Rejection.NonceTooHigh.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_transaction_requires_chain_id :
    LegacyCall.run 100 SpecId.CANCUN
      (blob_tx <| TransactionAccounting.Transaction.chain_id := None |>) (blob_input [0]) =
    LegacyCall.Result.Rejected LegacyCall.Rejection.MissingChainId.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_price_rejection_precedes_empty_hashes :
    LegacyCall.run 100 SpecId.CANCUN
      (blob_tx <| TransactionAccounting.Transaction.max_fee_per_blob_gas := 1 |>
        <| TransactionAccounting.Transaction.blob_hashes := [] |>) (blob_input [0]) =
    LegacyCall.Result.Rejected (LegacyCall.Rejection.Gas
      (TransactionAccounting.GasError.BlobGasPriceGreaterThanMax 2 1)).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_version_rejection_precedes_configured_count_limit :
    LegacyCall.run 100 SpecId.CANCUN
      (blob_tx <| TransactionAccounting.Transaction.blob_hashes := [blob_hash; 0] |>)
      ((blob_input [0]) <| LegacyCall.Input.max_blobs_per_tx := Some 1 |>) =
    LegacyCall.Result.Rejected (LegacyCall.Rejection.Gas TransactionAccounting.GasError.BlobVersionNotSupported).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_configured_count_limit_precedes_affordability :
    LegacyCall.run 100 SpecId.CANCUN
      (blob_tx <| TransactionAccounting.Transaction.blob_hashes := [blob_hash; blob_hash] |>)
      ((blob_input [0]) <| LegacyCall.Input.max_blobs_per_tx := Some 1 |>) =
    LegacyCall.Result.Rejected (LegacyCall.Rejection.Gas (TransactionAccounting.GasError.TooManyBlobs 2 1)).
  Proof. vm_compute. reflexivity. Qed.

  Lemma nonblob_transaction_ignores_blob_fee_and_hash_fields :
    observation (LegacyCall.run 100 SpecId.CANCUN
      (blob_tx <| TransactionAccounting.Transaction.tx_type := 2 |>) (blob_input [0])) =
    Some (InstructionResult.Stop, 21000, 1, 873993, 7, 42000, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma nonblob_transaction_blobhash_opcode_returns_zero :
    observation (LegacyCall.run 100 SpecId.CANCUN
      (blob_tx <| TransactionAccounting.Transaction.tx_type := 2 |>)
      (blob_input [96; 0; 73; 95; 85; 0])) =
    Some (InstructionResult.Stop, 21208, 1, 872745, 7, 42416, 0).
  Proof. vm_compute. reflexivity. Qed.

  Definition historical_gas (spec : SpecId.t) (code : list Z) : option Z :=
    match LegacyCall.run 100 spec tx (input code) with
    | LegacyCall.Result.Completed output =>
        Some output.(LegacyCall.Output.gas).(TransactionAccounting.Settlement.gas_used)
    | _ => None
    end.

  Lemma berlin_coinbase_starts_cold :
    historical_gas SpecId.BERLIN [96; 99; 49; 0] = Some 23603.
  Proof. vm_compute. reflexivity. Qed.

  Lemma london_coinbase_starts_cold :
    historical_gas SpecId.LONDON [96; 99; 49; 0] = Some 23603.
  Proof. vm_compute. reflexivity. Qed.

  Lemma paris_coinbase_starts_cold :
    historical_gas SpecId.MERGE [96; 99; 49; 0] = Some 23603.
  Proof. vm_compute. reflexivity. Qed.

  Lemma shanghai_coinbase_starts_warm :
    historical_gas SpecId.SHANGHAI [96; 99; 49; 0] = Some 21103.
  Proof. vm_compute. reflexivity. Qed.

  Lemma paris_push0_is_not_active :
    historical_gas SpecId.MERGE [95; 0] = Some 50000.
  Proof. vm_compute. reflexivity. Qed.

  Lemma shanghai_push0_is_active :
    historical_gas SpecId.SHANGHAI [95; 0] = Some 21002.
  Proof. vm_compute. reflexivity. Qed.

  Lemma petersburg_sload_cost :
    historical_gas SpecId.PETERSBURG [96; 0; 84; 0] = Some 21203.
  Proof. vm_compute. reflexivity. Qed.

  Lemma istanbul_sload_cost :
    historical_gas SpecId.ISTANBUL [96; 0; 84; 0] = Some 21803.
  Proof. vm_compute. reflexivity. Qed.

  Lemma petersburg_balance_cost :
    historical_gas SpecId.PETERSBURG [96; 99; 49; 0] = Some 21403.
  Proof. vm_compute. reflexivity. Qed.

  Lemma istanbul_balance_cost :
    historical_gas SpecId.ISTANBUL [96; 99; 49; 0] = Some 21703.
  Proof. vm_compute. reflexivity. Qed.

  Lemma petersburg_sstore_noop_uses_legacy_price :
    historical_gas SpecId.PETERSBURG [96; 1; 96; 0; 85; 0] = Some 26006.
  Proof. vm_compute. reflexivity. Qed.

  Lemma istanbul_sstore_noop_uses_net_metering :
    historical_gas SpecId.ISTANBUL [96; 1; 96; 0; 85; 0] = Some 21806.
  Proof. vm_compute. reflexivity. Qed.

  Lemma petersburg_clear_restore_keeps_legacy_clear_refund :
    historical_gas SpecId.PETERSBURG [96; 0; 96; 0; 85; 96; 1; 96; 0; 85; 0] =
      Some 31012.
  Proof. vm_compute. reflexivity. Qed.

  Lemma istanbul_clear_restore_uses_original_slot_refund :
    historical_gas SpecId.ISTANBUL [96; 0; 96; 0; 85; 96; 1; 96; 0; 85; 0] =
      Some 22612.
  Proof. vm_compute. reflexivity. Qed.

  Lemma petersburg_chainid_is_not_active :
    historical_gas SpecId.PETERSBURG [70; 0] = Some 50000.
  Proof. vm_compute. reflexivity. Qed.

  Lemma istanbul_chainid_is_active :
    historical_gas SpecId.ISTANBUL [70; 0] = Some 21002.
  Proof. vm_compute. reflexivity. Qed.

  Lemma petersburg_selfbalance_is_not_active :
    historical_gas SpecId.PETERSBURG [71; 0] = Some 50000.
  Proof. vm_compute. reflexivity. Qed.

  Lemma istanbul_selfbalance_is_active :
    historical_gas SpecId.ISTANBUL [71; 0] = Some 21005.
  Proof. vm_compute. reflexivity. Qed.

  Lemma petersburg_shift_is_active :
    historical_gas SpecId.PETERSBURG [96; 1; 96; 1; 27; 0] = Some 21009.
  Proof. vm_compute. reflexivity. Qed.

  Lemma unpinned_constantinople_still_reports_unsupported :
    LegacyCall.run 100 SpecId.CONSTANTINOPLE tx (input [0]) =
      LegacyCall.Result.Unsupported (LegacyCall.Gap.Accounting
        (TransactionAccounting.UnsupportedReason.Fork SpecId.CONSTANTINOPLE)).
  Proof. reflexivity. Qed.

  (** Test the execution boundary independently of the historical fork gate. *)
  Definition address_five_transaction (spec : SpecId.t) :=
    let transaction := tx <| TransactionAccounting.Transaction.target := Some 5 |> in
    let environment := input [] in
    let environment := environment <| LegacyCall.Input.accounts :=
      StatefulHost.update_account 5
        (fun account => account <| StatefulHost.Account.code := [96; 7; 96; 0; 85; 0] |>)
        environment.(LegacyCall.Input.accounts) |> in
    let block := {|
      TransactionAccounting.Block.gas_limit :=
        environment.(LegacyCall.Input.block).(StatefulHost.Environment.Block.gas_limit);
      TransactionAccounting.Block.base_fee :=
        environment.(LegacyCall.Input.block).(StatefulHost.Environment.Block.base_fee);
      TransactionAccounting.Block.blob_base_fee :=
        environment.(LegacyCall.Input.block).(StatefulHost.Environment.Block.blob_base_fee);
    |} in
    match TransactionAccounting.prepare_gas spec transaction block with
    | TransactionAccounting.Result.Ready initial =>
      match LegacyCall.execute 100 spec transaction environment (Some 5) initial with
      | LegacyCall.Result.Completed output =>
        Some (StatefulHost.lookup_word 0
          (LegacyCall.account_at 5 output.(LegacyCall.Output.accounts)).(StatefulHost.Account.storage))
      | _ => None
      end
    | _ => None
    end.

  Lemma top_level_address_five_executes_code_before_byzantium :
    address_five_transaction SpecId.SPURIOUS_DRAGON = Some 7.
  Proof. vm_compute. reflexivity. Qed.

  Lemma top_level_address_five_bypasses_code_from_byzantium :
    address_five_transaction SpecId.BYZANTIUM = Some 0.
  Proof. vm_compute. reflexivity. Qed.

End Test.
