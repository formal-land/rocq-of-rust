From Stdlib Require Import List ZArith.
Require Import alloy_eip7702.simulate.auth_list.
Require Import revm.revm_handler.simulate.legacy_call.
Require Import revm.revm_handler.simulate.transaction_accounting.
Require Import revm.revm_handler.tests.legacy_call.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_primitives.links.hardfork.
Require Import simulate.RocqOfRust.
Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition designation (address : Z) := [239; 1; 0] ++ List.repeat 0 19 ++ [address].

  Definition input (authority_code delegate_code : list Z) :=
    let environment := legacy_call.Test.input authority_code in
    environment <| LegacyCall.Input.accounts :=
      StatefulHost.update_account 43
        (fun account => account <| StatefulHost.Account.code := delegate_code |>)
        environment.(LegacyCall.Input.accounts) |>.

  Definition run (authority_code delegate_code : list Z) :=
    LegacyCall.run 100 SpecId.OSAKA legacy_call.Test.tx (input authority_code delegate_code).

  Definition slot (address : Z) (result : LegacyCall.Result.t) :=
    match result with
    | LegacyCall.Result.Completed output => Some (StatefulHost.lookup_word 0
      (LegacyCall.account_at address output.(LegacyCall.Output.accounts)).(StatefulHost.Account.storage))
    | _ => None
    end.

  Lemma legacy_transaction_executes_delegated_code_at_original_address :
    slot 42 (run (designation 43) [48; 95; 85; 0]) = Some 42.
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegated_execution_does_not_write_delegate_storage :
    slot 43 (run (designation 43) [48; 95; 85; 0]) = Some 0.
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegated_sender_is_accepted :
    let environment := legacy_call.Test.input [0] in
    let environment := environment <| LegacyCall.Input.accounts :=
      StatefulHost.update_account 100
        (fun account => account <| StatefulHost.Account.code := designation 43 |>)
        environment.(LegacyCall.Input.accounts) |> in
    legacy_call.Test.observation (LegacyCall.run 100 SpecId.OSAKA legacy_call.Test.tx environment) =
      Some (InstructionResult.Stop, 21000, 1, 789993, 7, 126000, 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma self_delegation_does_not_recurse :
    match run (designation 42) [] with
    | LegacyCall.Result.Completed output => Some output.(LegacyCall.Output.gas).(TransactionAccounting.Settlement.gas_used)
    | _ => None
    end = Some 50000.
  Proof. vm_compute. reflexivity. Qed.

  Definition invalid_authorization : SignedAuthorization.t := {|
    SignedAuthorization.inner := {|
      Authorization.chain_id := StatefulHost.rust_word 1;
      Authorization.address := StatefulHost.rust_address 43;
      Authorization.nonce := {| Integer.value := 0 |} |};
    SignedAuthorization.y_parity := {| Integer.value := 2 |};
    SignedAuthorization.r := StatefulHost.rust_word 1;
    SignedAuthorization.s := StatefulHost.rust_word 1;
  |}.

  Lemma invalid_parity_is_skipped_but_charges_intrinsic :
    legacy_call.Test.observation (LegacyCall.run 100 SpecId.OSAKA
      (legacy_call.Test.tx <| TransactionAccounting.Transaction.tx_type := 4 |>
        <| TransactionAccounting.Transaction.max_priority_fee := Some 6 |>
        <| TransactionAccounting.Transaction.authorization_list := [invalid_authorization] |>)
      (legacy_call.Test.input [0])) =
      Some (InstructionResult.Stop, 46000, 1, 539993, 7, 276000, 1).
  Proof. vm_compute. reflexivity. Qed.
End Test.
