From Stdlib Require Import List ZArith.
Require Import simulate.RocqOfRust.
Require Import alloy_primitives.utils.simulate.keccak256.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.simulate.address_creation.
Require Import revm.revm_handler.simulate.eest_types.
Require Import revm.revm_handler.simulate.transaction_accounting.
Require Import revm.revm_primitives.links.hardfork.
Import ListNotations.
Open Scope Z_scope.

Module TransactionCases.
  Definition block : EestTypes.Block.t := {|
    EestTypes.Block.coinbase := 0;
    EestTypes.Block.gas_limit := 1000000;
    EestTypes.Block.number := 0;
    EestTypes.Block.timestamp := 0;
    EestTypes.Block.difficulty := 0;
    EestTypes.Block.base_fee := 0;
    EestTypes.Block.blob_base_fee := 0;
    EestTypes.Block.previous_randao := None;
    EestTypes.Block.hashes := [];
    EestTypes.Block.use_state_test_hashes := false;
  |}.

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
    TransactionAccounting.Transaction.authorization_list := [];
    TransactionAccounting.Transaction.blob_hashes := [];
    TransactionAccounting.Transaction.value := 7;
    TransactionAccounting.Transaction.data := [];
  |}.

  Definition input (code : list Z) : EestTypes.Input.t := {|
    EestTypes.Input.chain_id := 1;
    EestTypes.Input.block := block
      <| EestTypes.Block.coinbase := 99 |>
      <| EestTypes.Block.base_fee := 4 |>
      <| EestTypes.Block.previous_randao := Some 0 |>;
    EestTypes.Input.excess_blob_gas := Some 0;
    EestTypes.Input.max_blobs_per_tx := None;
    EestTypes.Input.accounts :=
      [(EestTypes.empty_account 100) <| EestTypes.Account.balance := 1000000 |>;
       (EestTypes.empty_account 42) <| EestTypes.Account.nonce := 1 |>
         <| EestTypes.Account.code := code |>
         <| EestTypes.Account.code_hash :=
           List.fold_left (fun value byte => 256 * value + byte)
             (Keccak256.hash code) 0 |>
         <| EestTypes.Account.storage := [(0, 1)] |>;
       EestTypes.empty_account 77];
  |}.

  Definition observation (result : EestTypes.Result.t) :=
    match result with
    | EestTypes.Result.Completed output =>
      let sender := EestTypes.account_at 100 output.(EestTypes.Output.accounts) in
      let target := EestTypes.account_at 42 output.(EestTypes.Output.accounts) in
      let coinbase := EestTypes.account_at 99 output.(EestTypes.Output.accounts) in
      Some (output.(EestTypes.Output.status),
        output.(EestTypes.Output.gas).(TransactionAccounting.Settlement.gas_used),
        sender.(EestTypes.Account.nonce), sender.(EestTypes.Account.balance),
        target.(EestTypes.Account.balance), coinbase.(EestTypes.Account.balance),
        EestTypes.lookup_word 0 target.(EestTypes.Account.storage))
    | _ => None
    end.

  Definition access_list_tx (entries : list (Z * list Z)) :=
    tx <| TransactionAccounting.Transaction.tx_type := 1 |>
       <| TransactionAccounting.Transaction.access_list := entries |>.

  Definition dynamic_fee_tx :=
    tx <| TransactionAccounting.Transaction.tx_type := 2 |>
       <| TransactionAccounting.Transaction.max_priority_fee := Some 2 |>.

  Definition blob_hash : Z := 2 ^ 248 + 17.

  Definition blob_tx := dynamic_fee_tx
    <| TransactionAccounting.Transaction.tx_type := 3 |>
    <| TransactionAccounting.Transaction.max_fee_per_blob_gas := 3 |>
    <| TransactionAccounting.Transaction.blob_hashes := [blob_hash] |>.

  Definition blob_input (code : list Z) :=
    let source := input code in
    source <| EestTypes.Input.block := source.(EestTypes.Input.block)
      <| EestTypes.Block.blob_base_fee := 2 |> |>.

  Definition input_with_max_nonce (code : list Z) :=
    let source := input code in
    source <| EestTypes.Input.accounts :=
      EestTypes.update_account 100 (fun account =>
        account <| EestTypes.Account.nonce := 2 ^ 64 - 1 |>)
        source.(EestTypes.Input.accounts) |>.

End TransactionCases.

Module CreationCases.
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
    TransactionAccounting.Transaction.authorization_list := [];
    TransactionAccounting.Transaction.blob_hashes := [];
    TransactionAccounting.Transaction.value := 7;
    TransactionAccounting.Transaction.data := init_code;
  |}.

  Definition input : EestTypes.Input.t := {|
    EestTypes.Input.chain_id := 1;
    EestTypes.Input.block := TransactionCases.block
      <| EestTypes.Block.coinbase := 99 |>
      <| EestTypes.Block.base_fee := 4 |>
      <| EestTypes.Block.previous_randao := Some 0 |>;
    EestTypes.Input.excess_blob_gas := Some 0;
    EestTypes.Input.max_blobs_per_tx := None;
    EestTypes.Input.accounts :=
      [(EestTypes.empty_account 100) <| EestTypes.Account.balance := 1000000 |>];
  |}.

  Definition created_address : Z :=
    (Impl_AddressCreation.create {| Address.value := 100 |} (0 : u64)).(Address.value).

  Definition observation (result : EestTypes.Result.t) :=
    match result with
    | EestTypes.Result.Completed output =>
      let sender := EestTypes.account_at 100 output.(EestTypes.Output.accounts) in
      let coinbase := EestTypes.account_at 99 output.(EestTypes.Output.accounts) in
      let created := option_map (fun account =>
        (account.(EestTypes.Account.nonce), account.(EestTypes.Account.balance),
         account.(EestTypes.Account.code), account.(EestTypes.Account.storage),
         account.(EestTypes.Account.transient_storage)))
        (EestTypes.find_account created_address output.(EestTypes.Output.accounts)) in
      Some (output.(EestTypes.Output.status),
        output.(EestTypes.Output.gas).(TransactionAccounting.Settlement.gas_used),
        sender.(EestTypes.Account.nonce), sender.(EestTypes.Account.balance),
        coinbase.(EestTypes.Account.balance), created,
        output.(EestTypes.Output.data), output.(EestTypes.Output.logs))
    | _ => None
    end.

End CreationCases.
