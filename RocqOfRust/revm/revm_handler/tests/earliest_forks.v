From Stdlib Require Import List ZArith.

Require Import revm.revm_handler.simulate.legacy_call.
Require Import revm.revm_handler.simulate.transaction_accounting.
Require Import revm.revm_handler.tests.legacy_call.
Require Import revm.revm_handler.tests.legacy_create.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_primitives.links.hardfork.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Module C := legacy_call.Test.

  Module Creation := legacy_create.Test.

  Lemma frontier_homestead_sload_price :
    List.map (fun spec => C.historical_gas spec [96; 0; 84; 0])
      [SpecId.FRONTIER; SpecId.HOMESTEAD; SpecId.TANGERINE; SpecId.SPURIOUS_DRAGON; SpecId.BYZANTIUM] =
      [Some 21053; Some 21053; Some 21203; Some 21203; Some 21203].
  Proof. vm_compute. reflexivity. Qed.

  Lemma eip160_exponent_byte_price :
    List.map (fun spec => C.historical_gas spec [96; 1; 96; 2; 10; 0])
      [SpecId.FRONTIER; SpecId.HOMESTEAD; SpecId.TANGERINE; SpecId.SPURIOUS_DRAGON] =
      [Some 21026; Some 21026; Some 21026; Some 21066].
  Proof. vm_compute. reflexivity. Qed.

  Lemma oversized_call_gas_before_and_after_eip150 :
    List.map (fun spec => C.historical_gas spec (C.nested_call 77 0 65535 ++ [0]))
      [SpecId.FRONTIER; SpecId.HOMESTEAD; SpecId.TANGERINE; SpecId.SPURIOUS_DRAGON] =
      [Some 50000; Some 50000; Some 21721; Some 21721].
  Proof. vm_compute. reflexivity. Qed.

  Lemma missing_zero_value_call_new_account_price :
    List.map (fun spec => C.historical_gas spec (C.nested_call 78 0 0 ++ [0]))
      [SpecId.FRONTIER; SpecId.HOMESTEAD; SpecId.TANGERINE; SpecId.SPURIOUS_DRAGON] =
      [Some 46061; Some 46061; Some 46721; Some 21721].
  Proof. vm_compute. reflexivity. Qed.

  Lemma existing_empty_zero_value_call_is_not_new_before_eip161 :
    List.map (fun spec => C.historical_gas spec (C.nested_call 77 0 0 ++ [0]))
      [SpecId.FRONTIER; SpecId.HOMESTEAD; SpecId.TANGERINE; SpecId.SPURIOUS_DRAGON] =
      [Some 21061; Some 21061; Some 21721; Some 21721].
  Proof. vm_compute. reflexivity. Qed.

  Definition target_exists (spec : SpecId.t) : option bool :=
    match LegacyCall.run 100 spec
      (C.tx <| TransactionAccounting.Transaction.target := Some 78 |>
            <| TransactionAccounting.Transaction.value := 0 |>) (C.input []) with
    | LegacyCall.Result.Completed output => Some
        (match StatefulHost.find_account 78 output.(LegacyCall.Output.accounts) with
        | Some _ => true | None => false end)
    | _ => None
    end.

  Lemma top_level_zero_value_touch_persists_only_before_eip161 :
    List.map target_exists
      [SpecId.FRONTIER; SpecId.HOMESTEAD; SpecId.TANGERINE; SpecId.SPURIOUS_DRAGON; SpecId.BYZANTIUM] =
      [Some true; Some true; Some true; Some false; Some false].
  Proof. vm_compute. reflexivity. Qed.

  Lemma revert_is_enabled_at_byzantium :
    List.map (fun spec => C.historical_gas spec [96; 0; 96; 0; 253])
      [SpecId.SPURIOUS_DRAGON; SpecId.BYZANTIUM] = [Some 50000; Some 21006].
  Proof. vm_compute. reflexivity. Qed.

  Lemma returndata_is_enabled_at_byzantium :
    List.map (fun spec => C.historical_gas spec [61; 0])
      [SpecId.SPURIOUS_DRAGON; SpecId.BYZANTIUM] = [Some 50000; Some 21002].
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegatecall_is_enabled_at_homestead :
    List.map (fun spec => C.historical_gas spec (C.nested_delegatecall 77 0 ++ [0]))
      [SpecId.FRONTIER; SpecId.HOMESTEAD; SpecId.TANGERINE] =
      [Some 50000; Some 21058; Some 21718].
  Proof. vm_compute. reflexivity. Qed.

  Definition creation_observation (result : LegacyCall.Result.t) :=
    match result with
    | LegacyCall.Result.Completed output =>
      Some (output.(LegacyCall.Output.status),
        output.(LegacyCall.Output.gas).(TransactionAccounting.Settlement.gas_used),
        option_map (fun account =>
          (account.(StatefulHost.Account.nonce), account.(StatefulHost.Account.code)))
          (StatefulHost.find_account Creation.created_address output.(LegacyCall.Output.accounts)))
    | _ => None
    end.

  Lemma frontier_creation_has_no_homestead_intrinsic_surcharge :
    creation_observation (LegacyCall.run 100 SpecId.FRONTIER (Creation.tx [0]) Creation.input) =
      Some (InstructionResult.Return, 21004, Some (0, [])).
  Proof. vm_compute. reflexivity. Qed.

  Lemma homestead_creation_has_surcharge_but_zero_created_nonce :
    creation_observation (LegacyCall.run 100 SpecId.HOMESTEAD (Creation.tx [0]) Creation.input) =
      Some (InstructionResult.Return, 53004, Some (0, [])).
  Proof. vm_compute. reflexivity. Qed.

  Lemma spurious_creation_sets_created_nonce :
    creation_observation (LegacyCall.run 100 SpecId.SPURIOUS_DRAGON (Creation.tx [0]) Creation.input) =
      Some (InstructionResult.Return, 53004, Some (1, [])).
  Proof. vm_compute. reflexivity. Qed.

  Lemma frontier_code_deposit_oog_retains_empty_contract :
    creation_observation (LegacyCall.run 100 SpecId.FRONTIER
      ((Creation.tx [96; 1; 96; 0; 243])
        <| TransactionAccounting.Transaction.gas_limit := 21285 |>) Creation.input) =
      Some (InstructionResult.Return, 21285, Some (0, [])).
  Proof. vm_compute. reflexivity. Qed.

  Lemma homestead_code_deposit_oog_reverts_contract :
    creation_observation (LegacyCall.run 100 SpecId.HOMESTEAD
      ((Creation.tx [96; 1; 96; 0; 243])
        <| TransactionAccounting.Transaction.gas_limit := 53285 |>) Creation.input) =
      Some (InstructionResult.OutOfGas, 53285, None).
  Proof. vm_compute. reflexivity. Qed.
End Test.
