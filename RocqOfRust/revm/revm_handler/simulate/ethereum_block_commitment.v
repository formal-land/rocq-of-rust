From Stdlib Require Import Bool List ZArith.

Require Import alloy_primitives.utils.simulate.keccak256.
Require Import revm.revm_handler.simulate.ethereum_commitment.
Require Import revm.revm_handler.simulate.ethereum_rlp.
Require Import revm.revm_handler.simulate.eest_types.

Import ListNotations.
Open Scope Z_scope.

(** Consensus transaction and receipt trie commitments. Receipt creation and
    fork-specific validity decisions belong to the block executor. *)
Module EthereumBlockCommitment.
  Module Receipt.
    Module Outcome.
      Inductive t : Set :=
      | PostState (root : list Z)
      | Status (successful : bool).
    End Outcome.

    Record t : Set := {
      transaction_type : Z;
      outcome : Outcome.t;
      cumulative_gas_used : Z;
      logs : list EestTypes.EvmLog.t;
    }.
  End Receipt.

  Definition byte_valid (byte : Z) : bool := EthereumCommitment.bounded 8 byte.

  Definition bytes_valid (bytes : list Z) : bool := List.forallb byte_valid bytes.

  Definition bloom_item (bytes : list Z) : Z :=
    let hash := Keccak256.hash bytes in
    let byte_at := fun (index : nat) => List.nth index hash 0 in
    let bit := fun (index : nat) => Z.land (256 * byte_at index + byte_at (S index)) 2047 in
    Z.lor (Z.lor (Z.shiftl 1 (bit 0%nat)) (Z.shiftl 1 (bit 2%nat)))
      (Z.shiftl 1 (bit 4%nat)).

  Definition bloom_value (logs : list EestTypes.EvmLog.t) : Z :=
    List.fold_left (fun bloom log =>
      let address := EthereumRlp.fixed_big_endian 20
        log.(EestTypes.EvmLog.address) in
      let bloom := Z.lor bloom (bloom_item address) in
      List.fold_left (fun bloom topic =>
        Z.lor bloom (bloom_item (EthereumRlp.fixed_big_endian 32 topic)))
        log.(EestTypes.EvmLog.topics) bloom) logs 0.

  Definition logs_bloom (logs : list EestTypes.EvmLog.t) : option (list Z) :=
    if List.forallb EthereumCommitment.log_valid logs
    then Some (EthereumRlp.fixed_big_endian 256 (bloom_value logs))
    else None.

  Definition receipt_valid (receipt : Receipt.t) : bool :=
    EthereumCommitment.bounded 8 receipt.(Receipt.transaction_type) &&
    (receipt.(Receipt.transaction_type) <=? 4) &&
    EthereumCommitment.bounded 64 receipt.(Receipt.cumulative_gas_used) &&
    List.forallb EthereumCommitment.log_valid receipt.(Receipt.logs) &&
    match receipt.(Receipt.outcome) with
    | Receipt.Outcome.PostState root =>
        Nat.eqb (List.length root) 32 && bytes_valid root
    | Receipt.Outcome.Status _ => true
    end.

  Definition encode_log (log : EestTypes.EvmLog.t) : list Z :=
    EthereumRlp.encode_list [
      EthereumRlp.encode_bytes (EthereumRlp.fixed_big_endian 20
        log.(EestTypes.EvmLog.address));
      EthereumRlp.encode_list (List.map (fun topic =>
        EthereumRlp.encode_bytes (EthereumRlp.fixed_big_endian 32 topic))
        log.(EestTypes.EvmLog.topics));
      EthereumRlp.encode_bytes log.(EestTypes.EvmLog.data)].

  Definition receipt_bytes (receipt : Receipt.t) : option (list Z) :=
    if negb (receipt_valid receipt) then None else
    let outcome := match receipt.(Receipt.outcome) with
      | Receipt.Outcome.PostState root => EthereumRlp.encode_bytes root
      | Receipt.Outcome.Status true => EthereumRlp.encode_uint 1
      | Receipt.Outcome.Status false => EthereumRlp.encode_uint 0
      end in
    let body := EthereumRlp.encode_list [
      outcome;
      EthereumRlp.encode_uint receipt.(Receipt.cumulative_gas_used);
      EthereumRlp.encode_bytes (EthereumRlp.fixed_big_endian 256
        (bloom_value receipt.(Receipt.logs)));
      EthereumRlp.encode_list (List.map encode_log receipt.(Receipt.logs))] in
    if receipt.(Receipt.transaction_type) =? 0
    then Some body
    else Some (receipt.(Receipt.transaction_type) :: body).

  Fixpoint indexed (index : nat) (values : list (list Z)) :
      list (list Z * list Z) :=
    match values with
    | [] => []
    | value :: rest =>
        (EthereumRlp.encode_uint (Z.of_nat index), value) ::
          indexed (S index) rest
    end.

  Definition transaction_root (transactions : list (list Z)) : option (list Z) :=
    if List.forallb (fun raw => match raw with [] => false | _ => bytes_valid raw end)
        transactions
    then EthereumCommitment.Trie.root (indexed 0%nat transactions)
    else None.

  Fixpoint collect_receipts (index : nat) (receipts : list Receipt.t) :
      option (list (list Z * list Z)) :=
    match receipts with
    | [] => Some []
    | receipt :: rest =>
      match receipt_bytes receipt, collect_receipts (S index) rest with
      | Some encoded, Some entries =>
        Some ((EthereumRlp.encode_uint (Z.of_nat index), encoded) :: entries)
      | _, _ => None
      end
    end.

  Definition receipts_root (receipts : list Receipt.t) : option (list Z) :=
    match collect_receipts 0%nat receipts with
    | Some entries => EthereumCommitment.Trie.root entries
    | None => None
    end.

  Definition block_bloom (receipts : list Receipt.t) : option (list Z) :=
    if List.forallb receipt_valid receipts
    then Some (EthereumRlp.fixed_big_endian 256
      (bloom_value (List.concat (List.map Receipt.logs receipts))))
    else None.
End EthereumBlockCommitment.
