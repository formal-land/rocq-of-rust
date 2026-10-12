From Stdlib Require Import Bool List ZArith.

Require Import alloy_primitives.utils.simulate.keccak256.
Require Import revm.revm_handler.simulate.ethereum_rlp.
Require Import revm.revm_handler.simulate.ethereum_rlp_decode.

Import ListNotations.
Open Scope Z_scope.

(** Consensus RLP decoding for the pre-London Berlin block shape. The caller
    provides only raw genesis/block bytes. Fixture headers, expected validity
    and post-state are never inputs to these definitions. Transaction signatures,
    state transition and header validity belong to later layers. *)
Module BerlinBlockRlp.
  Module Malformed.
    Inductive t : Set :=
    | InvalidRlp
    | NonCanonicalRlp
    | BlockFields
    | HeaderFields
    | HeaderBytes
    | HeaderInteger
    | TransactionEnvelope.
  End Malformed.

  Module Unsupported.
    Inductive t : Set :=
    | FutureBlockBody
    | FutureHeader
    | NonemptyUncles
    | TransactionType (tx_type : Z).
  End Unsupported.

  Module DecodeResult.
    Inductive t (A : Set) : Set :=
    | Decoded (value : A)
    | Malformed (reason : Malformed.t)
    | Unsupported (reason : Unsupported.t).

    Arguments Decoded {A}.
    Arguments Malformed {A}.
    Arguments Unsupported {A}.
  End DecodeResult.

  Module Header.
    Record t : Set := {
      parent_hash : list Z;
      uncle_hash : list Z;
      coinbase : list Z;
      state_root : list Z;
      transactions_root : list Z;
      receipts_root : list Z;
      bloom : list Z;
      difficulty : Z;
      number : Z;
      gas_limit : Z;
      gas_used : Z;
      timestamp : Z;
      extra_data : list Z;
      mix_hash : list Z;
      nonce : list Z;
      raw_rlp : list Z;
    }.
  End Header.

  Module Transaction.
    Record t : Set := {
      tx_type : Z;
      raw : list Z;
    }.
  End Transaction.

  Module Block.
    Record t : Set := {
      header : Header.t;
      transactions : list Transaction.t;
      raw_rlp : list Z;
    }.
  End Block.

  Fixpoint bytes_equal (left right : list Z) : bool :=
    match left, right with
    | [], [] => true
    | x :: xs, y :: ys => (x =? y) && bytes_equal xs ys
    | _, _ => false
    end.

  Definition fixed_bytes (width : nat) (item : EthereumRlp.Item.t) : option (list Z) :=
    match item with
    | EthereumRlp.Item.Bytes bytes =>
        if Nat.eqb (List.length bytes) width then Some bytes else None
    | _ => None
    end.

  Definition uint (item : EthereumRlp.Item.t) : option Z :=
    match item with
    | EthereumRlp.Item.Bytes [] => Some 0
    | EthereumRlp.Item.Bytes (first :: rest) =>
        if first =? 0 then None else
        Some (List.fold_left (fun acc byte => 256 * acc + byte)
          (first :: rest) 0)
    | _ => None
    end.

  Definition bytes (item : EthereumRlp.Item.t) : option (list Z) :=
    match item with
    | EthereumRlp.Item.Bytes value => Some value
    | _ => None
    end.

  Definition uint64 (item : EthereumRlp.Item.t) : option Z :=
    match uint item with
    | Some value => if value <? 2 ^ 64 then Some value else None
    | None => None
    end.

  Definition decode_header (item : EthereumRlp.Item.t) : DecodeResult.t Header.t :=
    match item with
    | EthereumRlp.Item.List
        [parent; uncles; beneficiary; state; transactions; receipts; bloom;
         difficulty; number; gas_limit; gas_used; timestamp; extra; mix; nonce] =>
        match fixed_bytes 32 parent, fixed_bytes 32 uncles,
          fixed_bytes 20 beneficiary, fixed_bytes 32 state,
          fixed_bytes 32 transactions, fixed_bytes 32 receipts,
          fixed_bytes 256 bloom, fixed_bytes 32 mix, fixed_bytes 8 nonce with
        | Some parent_hash, Some uncle_hash, Some coinbase,
          Some state_root, Some transactions_root, Some receipts_root,
          Some bloom_bytes, Some mix_hash, Some nonce_bytes =>
            match uint difficulty, uint number,
              uint64 gas_limit, uint64 gas_used, uint64 timestamp,
              bytes extra with
            | Some difficulty_value, Some number_value, Some gas_limit_value,
              Some gas_used_value, Some timestamp_value, Some extra_data =>
                DecodeResult.Decoded {|
                  Header.parent_hash := parent_hash;
                  Header.uncle_hash := uncle_hash;
                  Header.coinbase := coinbase;
                  Header.state_root := state_root;
                  Header.transactions_root := transactions_root;
                  Header.receipts_root := receipts_root;
                  Header.bloom := bloom_bytes;
                  Header.difficulty := difficulty_value;
                  Header.number := number_value;
                  Header.gas_limit := gas_limit_value;
                  Header.gas_used := gas_used_value;
                  Header.timestamp := timestamp_value;
                  Header.extra_data := extra_data;
                  Header.mix_hash := mix_hash;
                  Header.nonce := nonce_bytes;
                  Header.raw_rlp := EthereumRlp.encode item;
                |}
            | _, _, _, _, _, _ => DecodeResult.Malformed Malformed.HeaderInteger
            end
        | _, _, _, _, _, _, _, _, _ => DecodeResult.Malformed Malformed.HeaderBytes
        end
    | EthereumRlp.Item.List fields =>
        if Nat.ltb 15 (List.length fields) then
          DecodeResult.Unsupported Unsupported.FutureHeader
        else DecodeResult.Malformed Malformed.HeaderFields
    | _ => DecodeResult.Malformed Malformed.HeaderFields
    end.

  Definition decode_transaction (item : EthereumRlp.Item.t) :
      DecodeResult.t Transaction.t :=
    match item with
    | EthereumRlp.Item.List fields =>
        if Nat.eqb (List.length fields) 9 then
          DecodeResult.Decoded {|
            Transaction.tx_type := 0;
            Transaction.raw := EthereumRlp.encode item;
          |}
        else DecodeResult.Malformed Malformed.TransactionEnvelope
    | EthereumRlp.Item.Bytes [] =>
        DecodeResult.Malformed Malformed.TransactionEnvelope
    | EthereumRlp.Item.Bytes (tx_type :: rest) =>
        if negb (tx_type =? 1) then
          DecodeResult.Unsupported (Unsupported.TransactionType tx_type)
        else match EthereumRlpDecode.decode rest with
          | Some (EthereumRlp.Item.List fields) =>
              if Nat.eqb (List.length fields) 11 &&
                bytes_equal (EthereumRlp.encode (EthereumRlp.Item.List fields)) rest then
                DecodeResult.Decoded {|
                  Transaction.tx_type := 1;
                  Transaction.raw := tx_type :: rest;
                |}
              else DecodeResult.Malformed Malformed.TransactionEnvelope
          | _ => DecodeResult.Malformed Malformed.TransactionEnvelope
          end
    end.

  Fixpoint decode_transactions (items : list EthereumRlp.Item.t) :
      DecodeResult.t (list Transaction.t) :=
    match items with
    | [] => DecodeResult.Decoded []
    | item :: rest =>
        match decode_transaction item with
        | DecodeResult.Malformed reason => DecodeResult.Malformed reason
        | DecodeResult.Unsupported reason => DecodeResult.Unsupported reason
        | DecodeResult.Decoded tx =>
            match decode_transactions rest with
            | DecodeResult.Malformed reason => DecodeResult.Malformed reason
            | DecodeResult.Unsupported reason => DecodeResult.Unsupported reason
            | DecodeResult.Decoded txs => DecodeResult.Decoded (tx :: txs)
            end
        end
    end.

  Definition decode (raw : list Z) : DecodeResult.t Block.t :=
    match EthereumRlpDecode.decode raw with
    | None => DecodeResult.Malformed Malformed.InvalidRlp
    | Some item =>
        if negb (bytes_equal (EthereumRlp.encode item) raw) then
          DecodeResult.Malformed Malformed.NonCanonicalRlp
        else match item with
        | EthereumRlp.Item.List
            [header_item; EthereumRlp.Item.List tx_items; EthereumRlp.Item.List []] =>
            match decode_header header_item with
            | DecodeResult.Malformed reason => DecodeResult.Malformed reason
            | DecodeResult.Unsupported reason => DecodeResult.Unsupported reason
            | DecodeResult.Decoded header =>
                match decode_transactions tx_items with
                | DecodeResult.Malformed reason => DecodeResult.Malformed reason
                | DecodeResult.Unsupported reason => DecodeResult.Unsupported reason
                | DecodeResult.Decoded txs =>
                    DecodeResult.Decoded {|
                      Block.header := header;
                      Block.transactions := txs;
                      Block.raw_rlp := raw;
                    |}
                end
            end
        | EthereumRlp.Item.List
            [_; EthereumRlp.Item.List _; EthereumRlp.Item.List (_ :: _)] =>
            DecodeResult.Unsupported Unsupported.NonemptyUncles
        | EthereumRlp.Item.List (_ :: _ :: _ :: _ :: _) =>
            DecodeResult.Unsupported Unsupported.FutureBlockBody
        | _ => DecodeResult.Malformed Malformed.BlockFields
        end
    end.

  Definition header_hash (header : Header.t) : list Z :=
    Keccak256.hash header.(Header.raw_rlp).

  Definition transaction_hash (tx : Transaction.t) : list Z :=
    Keccak256.hash tx.(Transaction.raw).

  Definition empty_uncles_hash : list Z :=
    Keccak256.hash (EthereumRlp.encode_list []).

  Module Test.
    Definition minimal_header : EthereumRlp.Item.t :=
      EthereumRlp.Item.List [
        EthereumRlp.Item.Bytes (List.repeat 0 32);
        EthereumRlp.Item.Bytes (List.repeat 0 32);
        EthereumRlp.Item.Bytes (List.repeat 0 20);
        EthereumRlp.Item.Bytes (List.repeat 0 32);
        EthereumRlp.Item.Bytes (List.repeat 0 32);
        EthereumRlp.Item.Bytes (List.repeat 0 32);
        EthereumRlp.Item.Bytes (List.repeat 0 256);
        EthereumRlp.Item.Bytes [];
        EthereumRlp.Item.Bytes [];
        EthereumRlp.Item.Bytes [];
        EthereumRlp.Item.Bytes [];
        EthereumRlp.Item.Bytes [];
        EthereumRlp.Item.Bytes [];
        EthereumRlp.Item.Bytes (List.repeat 0 32);
        EthereumRlp.Item.Bytes (List.repeat 0 8)].

    Lemma berlin_header_shape :
      match decode_header minimal_header with
      | DecodeResult.Decoded header =>
          Nat.eqb (List.length header.(Header.parent_hash)) 32
      | _ => false
      end = true.
    Proof. reflexivity. Qed.

    Lemma empty_input :
      decode [] = DecodeResult.Malformed Malformed.InvalidRlp.
    Proof. reflexivity. Qed.

    Lemma noncanonical_single_byte :
      decode [129; 0] = DecodeResult.Malformed Malformed.InvalidRlp.
    Proof. reflexivity. Qed.

    Lemma empty_list_not_block :
      decode [192] = DecodeResult.Malformed Malformed.BlockFields.
    Proof. reflexivity. Qed.

    Lemma missing_header_fields :
      decode [195; 192; 192; 192] =
        DecodeResult.Malformed Malformed.HeaderFields.
    Proof. reflexivity. Qed.

    Lemma future_block_body :
      decode [196; 192; 192; 192; 192] =
        DecodeResult.Unsupported Unsupported.FutureBlockBody.
    Proof. reflexivity. Qed.

    Lemma nonempty_uncle_list :
      decode [196; 192; 192; 193; 192] =
        DecodeResult.Unsupported Unsupported.NonemptyUncles.
    Proof. reflexivity. Qed.

    Lemma typed_transaction_before_london :
      decode_transaction (EthereumRlp.Item.Bytes [2; 192]) =
        DecodeResult.Unsupported (Unsupported.TransactionType 2).
    Proof. reflexivity. Qed.

    Lemma typed_transaction_bad_payload :
      decode_transaction (EthereumRlp.Item.Bytes [1; 192]) =
        DecodeResult.Malformed Malformed.TransactionEnvelope.
    Proof. reflexivity. Qed.
  End Test.
End BerlinBlockRlp.
