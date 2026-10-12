From Stdlib Require Import Bool List ZArith.

Require Import revm.revm_handler.simulate.blockchain_berlin.
Require Import revm.revm_handler.simulate.ethereum_block_commitment.
Require Import revm.revm_handler.simulate.ethereum_commitment.
Require Import revm.revm_handler.simulate.legacy_call.
Require Import revm.revm_handler.simulate.transaction_accounting.
Require Import revm.revm_handler.simulate.transaction_auth.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_precompile.simulate.modexp.
Require Import revm.revm_primitives.links.hardfork.

Import ListNotations.
Open Scope Z_scope.

(** One canonical Berlin block on a known parent. The allocation and raw RLP
    are inputs; fixture headers, receipts, post-state and expected validity are
    deliberately absent. This is an executable test layer, not a native REVM
    or Geth equivalence proof. *)
Module BerlinBlockExecution.
  Module HeaderError.
    Inductive t : Set :=
    | GenesisShape
    | GenesisStateRoot
    | ParentHash
    | Number
    | Timestamp
    | ExtraData
    | GasLimit
    | GasUsed
    | Difficulty
    | UncleHash
    | TransactionsRoot
    | ReceiptsRoot
    | Bloom
    | StateRoot.
  End HeaderError.

  Module TransactionError.
    Inductive t : Set :=
    | Authentication (reason : TransactionAuth.Error.t)
    | Execution (reason : LegacyCall.Rejection.t)
    | GasPool.
  End TransactionError.

  Module Gap.
    Inductive t : Set :=
    | BlockShape (reason : BerlinBlockRlp.Unsupported.t)
    | Authentication (reason : TransactionAuth.Unsupported.t)
    | Execution (reason : LegacyCall.Gap.t).
  End Gap.

  Module Output.
    Record t : Set := {
      header : BerlinBlockRlp.Header.t;
      accounts : list StatefulHost.Account.t;
      receipts : list EthereumBlockCommitment.Receipt.t;
      gas_used : Z;
      hashes : list (Z * Z);
    }.
  End Output.

  Module Result.
    Inductive t : Set :=
    | Accepted (output : Output.t)
    | InvalidHeader (reason : HeaderError.t)
    | InvalidTransaction (index : nat) (reason : TransactionError.t)
    | MalformedBlock (reason : BerlinBlockRlp.Malformed.t)
    | Unsupported (reason : Gap.t)
    | InvalidAllocation
    | Incomplete.
  End Result.

  Module TransactionRun.
    Record t : Set := {
      accounts : list StatefulHost.Account.t;
      receipts : list EthereumBlockCommitment.Receipt.t;
      cumulative_gas_used : Z;
      remaining_gas : Z;
    }.
  End TransactionRun.

  Module TransactionResult.
    Inductive t : Set :=
    | Completed (output : TransactionRun.t)
    | Rejected (index : nat) (reason : TransactionError.t)
    | Unsupported (reason : Gap.t)
    | Malformed
    | Incomplete.
  End TransactionResult.

  Definition bytes_equal := BerlinBlockRlp.bytes_equal.

  Definition zero_bloom : list Z := List.repeat 0 256.

  (** Berlin includes Muir Glacier, whose difficulty bomb delay is nine
      million blocks. Geth subtracts delay - 1 from the parent number. *)
  Definition bomb_period (parent_number : Z) : Z :=
    Z.max 0 (parent_number - 8999999) / 100000.

  Definition berlin_difficulty
      (parent child : BerlinBlockRlp.Header.t) : Z :=
    let parent_difficulty := parent.(BerlinBlockRlp.Header.difficulty) in
    let adjustment :=
      if bytes_equal parent.(BerlinBlockRlp.Header.uncle_hash)
        BerlinBlockRlp.empty_uncles_hash then 1 else 2 in
    let factor := Z.max (adjustment -
      (child.(BerlinBlockRlp.Header.timestamp) -
       parent.(BerlinBlockRlp.Header.timestamp)) / 9) (-99) in
    let ordinary := Z.max 131072
      (parent_difficulty + parent_difficulty / 2048 * factor) in
    let period := bomb_period parent.(BerlinBlockRlp.Header.number) in
    ordinary + if 1 <? period then 2 ^ (period - 2) else 0.

  Definition check_genesis
      (header : BerlinBlockRlp.Header.t)
      (transactions : list BerlinBlockRlp.Transaction.t)
      (accounts : list StatefulHost.Account.t) : option HeaderError.t :=
    if negb (header.(BerlinBlockRlp.Header.number) =? 0) ||
      negb (header.(BerlinBlockRlp.Header.gas_used) =? 0) ||
      negb (Nat.eqb (List.length transactions) 0)
    then Some HeaderError.GenesisShape else
    match EthereumCommitment.state_root accounts,
      EthereumBlockCommitment.transaction_root [],
      EthereumBlockCommitment.receipts_root [] with
    | Some state_root, Some transactions_root, Some receipts_root =>
        if negb (bytes_equal state_root header.(BerlinBlockRlp.Header.state_root))
        then Some HeaderError.GenesisStateRoot else
        if negb (bytes_equal transactions_root
          header.(BerlinBlockRlp.Header.transactions_root)) ||
          negb (bytes_equal receipts_root
            header.(BerlinBlockRlp.Header.receipts_root)) ||
          negb (bytes_equal zero_bloom header.(BerlinBlockRlp.Header.bloom)) ||
          negb (bytes_equal BerlinBlockRlp.empty_uncles_hash
            header.(BerlinBlockRlp.Header.uncle_hash))
        then Some HeaderError.GenesisShape else None
    | _, _, _ => Some HeaderError.GenesisStateRoot
    end.

  Definition check_header
      (parent child : BerlinBlockRlp.Header.t) : option HeaderError.t :=
    if negb (bytes_equal child.(BerlinBlockRlp.Header.parent_hash)
        (BerlinBlockRlp.header_hash parent))
    then Some HeaderError.ParentHash else
    if negb (child.(BerlinBlockRlp.Header.number) =?
      parent.(BerlinBlockRlp.Header.number) + 1)
    then Some HeaderError.Number else
    if child.(BerlinBlockRlp.Header.timestamp) <=?
      parent.(BerlinBlockRlp.Header.timestamp)
    then Some HeaderError.Timestamp else
    if 32 <? Z.of_nat (List.length child.(BerlinBlockRlp.Header.extra_data))
    then Some HeaderError.ExtraData else
    if negb ((5000 <=? child.(BerlinBlockRlp.Header.gas_limit)) &&
      (child.(BerlinBlockRlp.Header.gas_limit) <=? 2 ^ 63 - 1) &&
      (Z.abs (child.(BerlinBlockRlp.Header.gas_limit) -
        parent.(BerlinBlockRlp.Header.gas_limit)) <?
        parent.(BerlinBlockRlp.Header.gas_limit) / 1024))
    then Some HeaderError.GasLimit else
    if child.(BerlinBlockRlp.Header.gas_limit) <?
      child.(BerlinBlockRlp.Header.gas_used)
    then Some HeaderError.GasUsed else
    if negb (child.(BerlinBlockRlp.Header.difficulty) =?
      berlin_difficulty parent child)
    then Some HeaderError.Difficulty else
    if negb (bytes_equal child.(BerlinBlockRlp.Header.uncle_hash)
      BerlinBlockRlp.empty_uncles_hash)
    then Some HeaderError.UncleHash else None.

  Definition block_environment
      (header : BerlinBlockRlp.Header.t) (hashes : list (Z * Z)) :
      StatefulHost.Environment.Block.t := {|
    StatefulHost.Environment.Block.coinbase :=
      Modexp.decode_be header.(BerlinBlockRlp.Header.coinbase);
    StatefulHost.Environment.Block.gas_limit :=
      header.(BerlinBlockRlp.Header.gas_limit);
    StatefulHost.Environment.Block.number :=
      header.(BerlinBlockRlp.Header.number);
    StatefulHost.Environment.Block.timestamp :=
      header.(BerlinBlockRlp.Header.timestamp);
    StatefulHost.Environment.Block.difficulty :=
      header.(BerlinBlockRlp.Header.difficulty);
    StatefulHost.Environment.Block.base_fee := 0;
    StatefulHost.Environment.Block.blob_base_fee := 0;
    StatefulHost.Environment.Block.previous_randao := None;
    StatefulHost.Environment.Block.hashes := hashes;
    StatefulHost.Environment.Block.use_state_test_hashes := false;
  |}.

  Definition successful (status : InstructionResult.t) : bool :=
    match status with
    | InstructionResult.Stop | InstructionResult.Return |
      InstructionResult.SelfDestruct => true
    | _ => false
    end.

  Fixpoint run_transactions
      (fuel : nat) (chain_id : Z)
      (block : StatefulHost.Environment.Block.t)
      (transactions : list BerlinBlockRlp.Transaction.t)
      (index : nat) (state : TransactionRun.t) : TransactionResult.t :=
    match transactions with
    | [] => TransactionResult.Completed state
    | raw :: rest =>
      match TransactionAuth.authenticate_for_spec SpecId.BERLIN chain_id None
        raw.(BerlinBlockRlp.Transaction.raw) with
      | TransactionAuth.Result.Rejected reason =>
          TransactionResult.Rejected index
            (TransactionError.Authentication reason)
      | TransactionAuth.Result.Unsupported reason =>
          TransactionResult.Unsupported (Gap.Authentication reason)
      | TransactionAuth.Result.Authenticated tx =>
          if state.(TransactionRun.remaining_gas) <?
            tx.(TransactionAccounting.Transaction.gas_limit)
          then TransactionResult.Rejected index TransactionError.GasPool else
          let input : LegacyCall.Input.t := {|
            LegacyCall.Input.chain_id := chain_id;
            LegacyCall.Input.block := block;
            LegacyCall.Input.excess_blob_gas := None;
            LegacyCall.Input.max_blobs_per_tx := None;
            LegacyCall.Input.accounts := state.(TransactionRun.accounts);
          |} in
          match LegacyCall.run fuel SpecId.BERLIN tx input with
          | LegacyCall.Result.Rejected reason =>
              TransactionResult.Rejected index
                (TransactionError.Execution reason)
          | LegacyCall.Result.Unsupported reason =>
              TransactionResult.Unsupported (Gap.Execution reason)
          | LegacyCall.Result.Malformed => TransactionResult.Malformed
          | LegacyCall.Result.Incomplete => TransactionResult.Incomplete
          | LegacyCall.Result.Completed output =>
              let gas_used :=
                output.(LegacyCall.Output.gas)
                  .(TransactionAccounting.Settlement.gas_used) in
              let cumulative := state.(TransactionRun.cumulative_gas_used) + gas_used in
              let receipt : EthereumBlockCommitment.Receipt.t := {|
                EthereumBlockCommitment.Receipt.transaction_type :=
                  raw.(BerlinBlockRlp.Transaction.tx_type);
                EthereumBlockCommitment.Receipt.outcome :=
                  EthereumBlockCommitment.Receipt.Outcome.Status
                    (successful output.(LegacyCall.Output.status));
                EthereumBlockCommitment.Receipt.cumulative_gas_used := cumulative;
                EthereumBlockCommitment.Receipt.logs :=
                  output.(LegacyCall.Output.logs);
              |} in
              run_transactions fuel chain_id block rest (S index) {|
                TransactionRun.accounts := output.(LegacyCall.Output.accounts);
                TransactionRun.receipts := state.(TransactionRun.receipts) ++ [receipt];
                TransactionRun.cumulative_gas_used := cumulative;
                TransactionRun.remaining_gas :=
                  state.(TransactionRun.remaining_gas) - gas_used;
              |}
          end
      end
    end.

  Definition block_reward : Z := 2000000000000000000.

  Definition reward_account
      (coinbase : Z) (accounts : list StatefulHost.Account.t) :
      option (list StatefulHost.Account.t) :=
    let balance := (LegacyCall.account_at coinbase accounts)
      .(StatefulHost.Account.balance) in
    if balance + block_reward <? 2 ^ 256 then
      Some (StatefulHost.update_account coinbase
        (fun account => StatefulHost.account_with_balance account
          (account.(StatefulHost.Account.balance) + block_reward)) accounts)
    else None.

  Definition check_commitments
      (header : BerlinBlockRlp.Header.t)
      (transactions : list BerlinBlockRlp.Transaction.t)
      (run : TransactionRun.t)
      (accounts : list StatefulHost.Account.t) : option HeaderError.t :=
    match EthereumBlockCommitment.transaction_root
      (List.map BerlinBlockRlp.Transaction.raw transactions),
      EthereumBlockCommitment.receipts_root run.(TransactionRun.receipts),
      EthereumBlockCommitment.block_bloom run.(TransactionRun.receipts),
      EthereumCommitment.state_root accounts with
    | Some transactions_root, Some receipts_root, Some bloom, Some state_root =>
        if negb (bytes_equal transactions_root
          header.(BerlinBlockRlp.Header.transactions_root))
        then Some HeaderError.TransactionsRoot else
        if negb (bytes_equal receipts_root
          header.(BerlinBlockRlp.Header.receipts_root))
        then Some HeaderError.ReceiptsRoot else
        if negb (bytes_equal bloom header.(BerlinBlockRlp.Header.bloom))
        then Some HeaderError.Bloom else
        if negb (bytes_equal state_root header.(BerlinBlockRlp.Header.state_root))
        then Some HeaderError.StateRoot else None
    | _, _, _, _ => Some HeaderError.StateRoot
    end.

  Definition import_decoded
      (fuel : nat) (chain_id : Z)
      (parent : BerlinBlockRlp.Header.t)
      (accounts : list StatefulHost.Account.t)
      (hashes : list (Z * Z))
      (block : BerlinBlockRlp.Block.t) : Result.t :=
    let header := block.(BerlinBlockRlp.Block.header) in
    match check_header parent header with
    | Some reason => Result.InvalidHeader reason
    | None =>
      match run_transactions fuel chain_id (block_environment header hashes)
        block.(BerlinBlockRlp.Block.transactions) 0%nat {|
          TransactionRun.accounts := accounts;
          TransactionRun.receipts := [];
          TransactionRun.cumulative_gas_used := 0;
          TransactionRun.remaining_gas := header.(BerlinBlockRlp.Header.gas_limit);
        |} with
      | TransactionResult.Rejected index reason =>
          Result.InvalidTransaction index reason
      | TransactionResult.Unsupported reason => Result.Unsupported reason
      | TransactionResult.Malformed => Result.InvalidAllocation
      | TransactionResult.Incomplete => Result.Incomplete
      | TransactionResult.Completed run =>
          if negb (run.(TransactionRun.cumulative_gas_used) =?
            header.(BerlinBlockRlp.Header.gas_used))
          then Result.InvalidHeader HeaderError.GasUsed else
          match reward_account
            (Modexp.decode_be header.(BerlinBlockRlp.Header.coinbase))
            run.(TransactionRun.accounts) with
          | None => Result.Incomplete
          | Some accounts =>
            match check_commitments header
              block.(BerlinBlockRlp.Block.transactions) run accounts with
            | Some reason => Result.InvalidHeader reason
            | None => Result.Accepted {|
                Output.header := header;
                Output.accounts := accounts;
                Output.receipts := run.(TransactionRun.receipts);
                Output.gas_used := run.(TransactionRun.cumulative_gas_used);
                Output.hashes := (header.(BerlinBlockRlp.Header.number),
                  Modexp.decode_be (BerlinBlockRlp.header_hash header)) :: hashes;
              |}
            end
          end
      end
    end.

  Definition import_block
      (fuel : nat) (chain_id : Z)
      (parent : BerlinBlockRlp.Header.t)
      (accounts : list StatefulHost.Account.t)
      (hashes : list (Z * Z)) (raw : list Z) : Result.t :=
    match BerlinBlockRlp.decode raw with
    | BerlinBlockRlp.DecodeResult.Malformed reason => Result.MalformedBlock reason
    | BerlinBlockRlp.DecodeResult.Unsupported reason =>
        Result.Unsupported (Gap.BlockShape reason)
    | BerlinBlockRlp.DecodeResult.Decoded block =>
        import_decoded fuel chain_id parent accounts hashes block
    end.

  Definition import_first
      (fuel : nat) (chain_id : Z)
      (accounts : list StatefulHost.Account.t)
      (genesis_raw block_raw : list Z) : Result.t :=
    if negb ((0 <=? chain_id) && (chain_id <? 2 ^ 64) &&
      List.forallb LegacyCall.account_valid accounts &&
      LegacyCall.distinct (List.map StatefulHost.Account.address accounts))
    then Result.InvalidAllocation else
    match BerlinBlockRlp.decode genesis_raw with
    | BerlinBlockRlp.DecodeResult.Malformed reason => Result.MalformedBlock reason
    | BerlinBlockRlp.DecodeResult.Unsupported reason =>
        Result.Unsupported (Gap.BlockShape reason)
    | BerlinBlockRlp.DecodeResult.Decoded genesis =>
        let parent := genesis.(BerlinBlockRlp.Block.header) in
        match check_genesis parent genesis.(BerlinBlockRlp.Block.transactions) accounts with
        | Some reason => Result.InvalidHeader reason
        | None => import_block fuel chain_id parent accounts
            [(0, Modexp.decode_be (BerlinBlockRlp.header_hash parent))] block_raw
        end
    end.

  Module Test.
    Lemma berlin_muir_glacier_bomb_boundary :
      bomb_period 9199998 = 1 /\ bomb_period 9199999 = 2.
    Proof. vm_compute. split; reflexivity. Qed.

    Lemma empty_block_reward_creates_coinbase :
      match reward_account 7 [] with
      | Some accounts =>
          match StatefulHost.find_account 7 accounts with
          | Some account => account.(StatefulHost.Account.balance) =? block_reward
          | None => false
          end
      | None => false
      end = true.
    Proof. vm_compute. reflexivity. Qed.

    Lemma reward_overflow_is_incomplete :
      reward_account 7 [StatefulHost.account_with_balance
        (StatefulHost.empty_account 7) (2 ^ 256 - 1)] = None.
    Proof. vm_compute. reflexivity. Qed.
  End Test.
End BerlinBlockExecution.
