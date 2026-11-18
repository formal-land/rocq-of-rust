From Stdlib Require Import List ZArith.

Require Import simulate.RocqOfRust.
Require Import alloy_primitives.utils.simulate.keccak256.
Require Import revm.revm_handler.simulate.transaction_accounting.
Require Import revm.revm_interpreter.links.instruction_result.

Import ListNotations.
Open Scope Z_scope.

(** JSON fixture records and validation. Execution uses the typed Context;
    unbounded fixture integers are checked before conversion to Rust types. *)
Module EestTypes.
  Module Block.
    Record t : Set := {
      coinbase : Z;
      gas_limit : Z;
      number : Z;
      timestamp : Z;
      difficulty : Z;
      base_fee : Z;
      blob_base_fee : Z;
      previous_randao : option Z;
      hashes : list (Z * Z);
      use_state_test_hashes : bool;
    }.
  End Block.

  Module Account.
    Record t : Set := {
      address : Z;
      balance : Z;
      nonce : Z;
      code : list Z;
      code_hash : Z;
      storage : list (Z * Z);
      transient_storage : list (Z * Z);
    }.
  End Account.

  Module EvmLog.
    Record t : Set := {
      address : Z;
      topics : list Z;
      data : list Z;
    }.
  End EvmLog.

  Fixpoint find_account
      (address : Z) (accounts : list Account.t) :
      option Account.t :=
    match accounts with
    | [] => None
    | account :: accounts =>
        if account.(Account.address) =? address
        then Some account
        else find_account address accounts
    end.

  Fixpoint lookup_word (key : Z) (entries : list (Z * Z)) : Z :=
    match entries with
    | [] => 0
    | (entry_key, value) :: entries =>
        if entry_key =? key then value else lookup_word key entries
    end.

  Fixpoint lookup_z (key : Z) (entries : list (Z * Z)) : option Z :=
    match entries with
    | [] => None
    | (entry_key, value) :: entries =>
        if entry_key =? key then Some value else lookup_z key entries
    end.

  Definition empty_code_hash : Z :=
    89477152217924674838424037953991966239322087453347756267410168184682657981552.

  Definition empty_account (address : Z) : Account.t :=
    {| Account.address := address;
       Account.balance := 0;
       Account.nonce := 0;
       Account.code := [];
       Account.code_hash := empty_code_hash;
       Account.storage := [];
       Account.transient_storage := [] |}.

  Fixpoint update_account
      (address : Z)
      (update : Account.t -> Account.t)
      (accounts : list Account.t) : list Account.t :=
    match accounts with
    | [] => [update (empty_account address)]
    | account :: accounts =>
        if account.(Account.address) =? address
        then update account :: accounts
        else account :: update_account address update accounts
    end.

  Fixpoint decimal_digits (fuel : nat) (value : Z) : list Z :=
    match fuel with
    | O => []
    | S rest =>
        if value <? 10 then [48 + value]
        else decimal_digits rest (value / 10) ++ [48 + value mod 10]
    end.

  Definition state_test_block_hash (number : Z) : Z :=
    let signed := if number <? 2 ^ 63 then number else number - 2 ^ 64 in
    let decimal := if signed <? 0 then 45 :: decimal_digits 20 (-signed)
      else decimal_digits 20 signed in
    List.fold_left (fun value byte => 256 * value + byte)
      (Keccak256.hash decimal) 0.

  Module Input.
    Record t : Set := {
      chain_id : Z;
      block : EestTypes.Block.t;
      excess_blob_gas : option Z;
      max_blobs_per_tx : option Z;
      accounts : list EestTypes.Account.t;
    }.
  End Input.

  Module Rejection.
    Inductive t : Set :=
    | Gas (reason : TransactionAccounting.GasError.t)
    | PrevrandaoNotSet
    | ExcessBlobGasNotSet
    | InvalidChainId
    | MissingChainId
    | RejectCallerWithCode
    | NonceTooLow
    | NonceTooHigh
    | NonceOverflow
    | LackOfFunds.
  End Rejection.

  Module Gap.
    Inductive t : Set :=
    | Accounting (reason : TransactionAccounting.UnsupportedReason.t)
    | TopLevelPrecompile
    | Delegation.
  End Gap.

  Module Output.
    Record t : Set := {
      status : InstructionResult.t;
      gas : TransactionAccounting.Settlement.t;
      data : list Z;
      accounts : list EestTypes.Account.t;
      logs : list EestTypes.EvmLog.t;
    }.
  End Output.

  Module Result.
    Inductive t : Set :=
    | Completed (output : Output.t)
    | Rejected (reason : Rejection.t)
    | Unsupported (reason : Gap.t)
    | Malformed
    | Incomplete.
  End Result.

  Fixpoint distinct (values : list Z) : bool :=
    match values with
    | [] => true
    | value :: rest => negb (List.existsb (Z.eqb value) rest) && distinct rest
    end.

  Definition account_valid (account : EestTypes.Account.t) : bool :=
    TransactionAccounting.bounded 160 account.(EestTypes.Account.address) &&
    TransactionAccounting.bounded 256 account.(EestTypes.Account.balance) &&
    TransactionAccounting.bounded 64 account.(EestTypes.Account.nonce) &&
    TransactionAccounting.bounded 256 account.(EestTypes.Account.code_hash) &&
    List.forallb (TransactionAccounting.bounded 8) account.(EestTypes.Account.code) &&
    List.forallb (fun slot => TransactionAccounting.bounded 256 (fst slot) &&
      TransactionAccounting.bounded 256 (snd slot)) account.(EestTypes.Account.storage) &&
    distinct (List.map fst account.(EestTypes.Account.storage)) &&
    match account.(EestTypes.Account.transient_storage) with
    | [] => true
    | _ => false
    end.

  Definition input_valid (input : Input.t) : bool :=
    TransactionAccounting.bounded 64 input.(Input.chain_id) &&
    TransactionAccounting.bounded 160 input.(Input.block).(EestTypes.Block.coinbase) &&
    TransactionAccounting.bounded 64 input.(Input.block).(EestTypes.Block.number) &&
    TransactionAccounting.bounded 64 input.(Input.block).(EestTypes.Block.timestamp) &&
    TransactionAccounting.bounded 256 input.(Input.block).(EestTypes.Block.difficulty) &&
    TransactionAccounting.bounded 128 input.(Input.block).(EestTypes.Block.blob_base_fee) &&
    List.forallb (fun entry => TransactionAccounting.bounded 64 (fst entry) &&
      TransactionAccounting.bounded 256 (snd entry)) input.(Input.block).(EestTypes.Block.hashes) &&
    (match input.(Input.block).(EestTypes.Block.previous_randao) with
     | None => true
     | Some value => TransactionAccounting.bounded 256 value
     end) &&
    (match input.(Input.excess_blob_gas) with
     | None => true
     | Some value => TransactionAccounting.bounded 64 value
     end) &&
    TransactionAccounting.blob_limit_valid input.(Input.max_blobs_per_tx) &&
    List.forallb account_valid input.(Input.accounts) &&
    distinct (List.map EestTypes.Account.address input.(Input.accounts)).

  Definition account_at (address : Z) (accounts : list EestTypes.Account.t) :=
    match EestTypes.find_account address accounts with
    | Some account => account
    | None => EestTypes.empty_account address
    end.

End EestTypes.
