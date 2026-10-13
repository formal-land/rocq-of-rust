From Stdlib Require Import List ZArith.

Require Import revm.revm_handler.simulate.legacy_call.
Require Import revm.revm_handler.simulate.transaction_accounting.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.tests.create_address.
Require Import revm.revm_interpreter.tests.stateful_dispatch.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_primitives.links.hardfork.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition tx (init_code : list Z) : TransactionAccounting.Transaction.t := {|
    TransactionAccounting.Transaction.tx_type := 0;
    TransactionAccounting.Transaction.caller := 100;
    TransactionAccounting.Transaction.target := None;
    TransactionAccounting.Transaction.nonce := 0;
    TransactionAccounting.Transaction.chain_id := Some 1;
    TransactionAccounting.Transaction.gas_limit := 80000;
    TransactionAccounting.Transaction.gas_price := 10;
    TransactionAccounting.Transaction.max_priority_fee := None;
    TransactionAccounting.Transaction.access_list := [];
    TransactionAccounting.Transaction.max_fee_per_blob_gas := 0;
    TransactionAccounting.Transaction.blob_hashes := [];
    TransactionAccounting.Transaction.value := 7;
    TransactionAccounting.Transaction.data := init_code;
  |}.

  Definition input : LegacyCall.Input.t := {|
    LegacyCall.Input.chain_id := 1;
    LegacyCall.Input.block := add11_input.(StatefulHost.Input.block)
      <| StatefulHost.Environment.Block.coinbase := 99 |>
      <| StatefulHost.Environment.Block.base_fee := 4 |>
      <| StatefulHost.Environment.Block.previous_randao := Some 0 |>;
    LegacyCall.Input.excess_blob_gas := Some 0;
    LegacyCall.Input.max_blobs_per_tx := None;
    LegacyCall.Input.accounts :=
      [(StatefulHost.empty_account 100) <| StatefulHost.Account.balance := 1000000 |>];
  |}.

  Definition created_address : Z :=
    match CreateAddress.create 100 0 with Some address => address | None => 0 end.

  Definition observation (result : LegacyCall.Result.t) :=
    match result with
    | LegacyCall.Result.Completed output =>
      let sender := LegacyCall.account_at 100 output.(LegacyCall.Output.accounts) in
      let coinbase := LegacyCall.account_at 99 output.(LegacyCall.Output.accounts) in
      let created := option_map (fun account =>
        (account.(StatefulHost.Account.nonce), account.(StatefulHost.Account.balance),
         account.(StatefulHost.Account.code), account.(StatefulHost.Account.storage),
         account.(StatefulHost.Account.transient_storage)))
        (StatefulHost.find_account created_address output.(LegacyCall.Output.accounts)) in
      Some (output.(LegacyCall.Output.status),
        output.(LegacyCall.Output.gas).(TransactionAccounting.Settlement.gas_used),
        sender.(StatefulHost.Account.nonce), sender.(StatefulHost.Account.balance),
        coinbase.(StatefulHost.Account.balance), created,
        output.(LegacyCall.Output.data), output.(LegacyCall.Output.logs))
    | _ => None
    end.

  Definition run (init_code : list Z) := LegacyCall.run 100 SpecId.CANCUN (tx init_code) input.

  Lemma stop_creates_empty_contract_and_charges_intrinsic :
    observation (run [0]) =
    Some (InstructionResult.Return, 53006, 1, 469933, 318036,
      Some (1, 7, [], [], []), [], []).
  Proof. vm_compute. reflexivity. Qed.

  Definition return_one_byte (byte : Z) := [96; byte; 95; 83; 96; 1; 95; 243].

  Lemma return_deploys_runtime_code_and_charges_deposit :
    observation (run (return_one_byte 0)) =
    Some (InstructionResult.Return, 53334, 1, 466653, 320004,
      Some (1, 7, [0], [], []), [0], []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma revert_preserves_nonce_and_fees_and_returns_payload :
    observation (run [96; 42; 95; 83; 96; 1; 95; 253]) =
    Some (InstructionResult.Revert, 53146, 1, 468540, 318876,
      None, [42], []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma revert_discards_created_storage_and_logs :
    observation (run [95; 95; 160; 96; 1; 95; 85; 95; 95; 253]) =
    Some (InstructionResult.Revert, 75650, 1, 243500, 453900,
      None, [], []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma collision_keeps_existing_account_and_consumes_all_gas :
    let source := input <| LegacyCall.Input.accounts := input.(LegacyCall.Input.accounts) ++
      [(StatefulHost.empty_account created_address) <| StatefulHost.Account.nonce := 1 |>
        <| StatefulHost.Account.balance := 11 |>] |> in
    observation (LegacyCall.run 100 SpecId.CANCUN (tx [0]) source) =
    Some (InstructionResult.CreateCollision, 80000, 1, 200000, 480000,
      Some (1, 11, [], [], []), [], []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma deposit_exact_gas_boundary_succeeds :
    observation (LegacyCall.run 100 SpecId.CANCUN
      ((tx (return_one_byte 0)) <| TransactionAccounting.Transaction.gas_limit := 53334 |>) input) =
    Some (InstructionResult.Return, 53334, 1, 466653, 320004,
      Some (1, 7, [0], [], []), [0], []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma deposit_one_gas_short_rolls_back_value_and_code :
    observation (LegacyCall.run 100 SpecId.CANCUN
      ((tx (return_one_byte 0)) <| TransactionAccounting.Transaction.gas_limit := 53333 |>) input) =
    Some (InstructionResult.OutOfGas, 53333, 1, 466670, 319998,
      None, [], []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma ef_prefix_rejection_rolls_back_creation :
    observation (run (return_one_byte 239)) =
    Some (InstructionResult.CreateContractStartingWithEF, 80000, 1, 200000, 480000,
      None, [], []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma oversized_runtime_rejection_rolls_back_creation :
    observation (run [97; 96; 1; 95; 243]) =
    Some (InstructionResult.CreateContractSizeLimit, 80000, 1, 200000, 480000,
      None, [], []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma maximum_initcode_size_is_inclusive :
    let source := input <| LegacyCall.Input.accounts :=
      [(StatefulHost.empty_account 100) <| StatefulHost.Account.balance := 10000000 |>] |> in
    observation (LegacyCall.run 100 SpecId.CANCUN
      ((tx (List.repeat 0 49152)) <| TransactionAccounting.Transaction.gas_limit := 300000 |>) source) =
    Some (InstructionResult.Return, 252680, 1, 7473193, 1516080,
      Some (1, 7, [], [], []), [], []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma oversized_initcode_rejected_before_intrinsic_gas :
    LegacyCall.run 100 SpecId.CANCUN (tx (List.repeat 0 49153)) input =
    LegacyCall.Result.Rejected (LegacyCall.Rejection.Gas
      TransactionAccounting.GasError.CreateInitCodeSizeLimit).
  Proof. vm_compute. reflexivity. Qed.

  Lemma prague_floor_applies_after_creation_intrinsic :
    let source := input <| LegacyCall.Input.accounts :=
      [(StatefulHost.empty_account 100) <| StatefulHost.Account.balance := 10000000 |>] |> in
    observation (LegacyCall.run 100 SpecId.PRAGUE
      ((tx (List.repeat 0 49152)) <| TransactionAccounting.Transaction.gas_limit := 600000 |>) source) =
    Some (InstructionResult.Return, 512520, 1, 4874793, 3075120,
      Some (1, 7, [], [], []), [], []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma intrinsic_exact_gas_boundary_succeeds :
    observation (LegacyCall.run 100 SpecId.CANCUN
      ((tx [0]) <| TransactionAccounting.Transaction.gas_limit := 53006 |>) input) =
    Some (InstructionResult.Return, 53006, 1, 469933, 318036,
      Some (1, 7, [], [], []), [], []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma intrinsic_one_gas_short_rejected_before_execution :
    LegacyCall.run 100 SpecId.CANCUN
      ((tx [0]) <| TransactionAccounting.Transaction.gas_limit := 53005 |>) input =
    LegacyCall.Result.Rejected (LegacyCall.Rejection.Gas
      (TransactionAccounting.GasError.IntrinsicGasTooHigh 53006 53005)).
  Proof. vm_compute. reflexivity. Qed.

  Lemma osaka_cap_precedes_initcode_size_rejection :
    LegacyCall.run 100 SpecId.OSAKA
      ((tx (List.repeat 0 49153)) <| TransactionAccounting.Transaction.gas_limit := 16777217 |>) input =
    LegacyCall.Result.Rejected (LegacyCall.Rejection.Gas
      (TransactionAccounting.GasError.GasLimitAboveCap 16777217 16777216)).
  Proof. vm_compute. reflexivity. Qed.

  Lemma nonce_overflow_returns_without_creating_or_incrementing :
    let source := input <| LegacyCall.Input.accounts :=
      [(StatefulHost.empty_account 100) <| StatefulHost.Account.balance := 1000000 |>
        <| StatefulHost.Account.nonce := 2 ^ 64 - 1 |>] |> in
    observation (LegacyCall.run 100 SpecId.CANCUN
      ((tx [0]) <| TransactionAccounting.Transaction.nonce := 2 ^ 64 - 1 |>) source) =
    Some (InstructionResult.Return, 53006, 2 ^ 64 - 1, 469940, 318036,
      None, [], []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_fee_creation_uses_effective_price_for_opcode_and_settlement :
    let source := input <| LegacyCall.Input.accounts :=
      [(StatefulHost.empty_account 100) <| StatefulHost.Account.balance := 2000000 |>] |> in
    observation (LegacyCall.run 100 SpecId.CANCUN
      ((tx [58; 95; 83; 96; 1; 95; 243])
        <| TransactionAccounting.Transaction.tx_type := 2 |>
        <| TransactionAccounting.Transaction.gas_price := 20 |>
        <| TransactionAccounting.Transaction.max_priority_fee := Some 3 |>) source) =
    Some (InstructionResult.Return, 53329, 1, 1626690, 159987,
      Some (1, 7, [7], [], []), [7], []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma normalized_blob_creation_preserves_native_handler_behavior :
    let source := input <| LegacyCall.Input.block := input.(LegacyCall.Input.block)
      <| StatefulHost.Environment.Block.blob_base_fee := 2 |> |> in
    observation (LegacyCall.run 100 SpecId.CANCUN
      ((tx [0]) <| TransactionAccounting.Transaction.tx_type := 3 |>
        <| TransactionAccounting.Transaction.gas_price := 6 |>
        <| TransactionAccounting.Transaction.max_priority_fee := Some 2 |>
        <| TransactionAccounting.Transaction.max_fee_per_blob_gas := 3 |>
        <| TransactionAccounting.Transaction.blob_hashes := [2 ^ 248 + 17] |>) source) =
    Some (InstructionResult.Return, 53006, 1, 419813, 106012,
      Some (1, 7, [], [], []), [], []).
  Proof. vm_compute. reflexivity. Qed.
End Test.
