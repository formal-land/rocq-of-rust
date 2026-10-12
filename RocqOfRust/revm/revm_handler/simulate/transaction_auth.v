From Stdlib Require Import Bool List ZArith.

Require Import alloy_primitives.utils.simulate.keccak256.
Require Import revm.revm_handler.simulate.ethereum_rlp.
Require Import revm.revm_handler.simulate.ethereum_rlp_decode.
Require Import revm.revm_handler.simulate.transaction_accounting.
Require Import revm.revm_precompile.simulate.modexp.
Require Import revm.revm_precompile.simulate.secp256k1.
Require Import revm.revm_primitives.links.hardfork.

Import ListNotations.
Open Scope Z_scope.

(** Canonical signed envelopes and sender recovery for the supported forks.
    TxEnv validation receives an already selected caller. This separate layer
    follows geth core/types/transaction_signing.go and tx_* signing hashes;
    it does not establish a native decoding or cryptographic morphism. *)
Module TransactionAuth.
  Fixpoint sequence {A : Set} (values : list (option A)) : option (list A) :=
    match values with
    | [] => Some []
    | Some value :: rest =>
        match sequence rest with
        | Some values => Some (value :: values)
        | None => None
        end
    | None :: _ => None
    end.

  Definition uint (item : EthereumRlp.Item.t) : option Z :=
    match item with
    | EthereumRlp.Item.Bytes [] => Some 0
    | EthereumRlp.Item.Bytes (first :: rest) =>
        if first =? 0 then None else Some (Modexp.decode_be (first :: rest))
    | _ => None
    end.

  Definition bytes (item : EthereumRlp.Item.t) : option (list Z) :=
    match item with
    | EthereumRlp.Item.Bytes value => Some value
    | _ => None
    end.

  Definition fixed_uint (width : nat) (item : EthereumRlp.Item.t) : option Z :=
    match bytes item with
    | Some value =>
        if Nat.eqb (List.length value) width then Some (Modexp.decode_be value) else None
    | None => None
    end.

  Definition target (item : EthereumRlp.Item.t) : option (option Z) :=
    match bytes item with
    | Some [] => Some None
    | Some value =>
        if Nat.eqb (List.length value) 20 then Some (Some (Modexp.decode_be value)) else None
    | None => None
    end.

  Definition access_entry (item : EthereumRlp.Item.t) : option (Z * list Z) :=
    match item with
    | EthereumRlp.Item.List [address; EthereumRlp.Item.List keys] =>
        match fixed_uint 20 address, sequence (List.map (fixed_uint 32) keys) with
        | Some address, Some keys => Some (address, keys)
        | _, _ => None
        end
    | _ => None
    end.

  Definition access_list (item : EthereumRlp.Item.t) : option (list (Z * list Z)) :=
    match item with
    | EthereumRlp.Item.List entries => sequence (List.map access_entry entries)
    | _ => None
    end.

  Definition blob_hashes (item : EthereumRlp.Item.t) : option (list Z) :=
    match item with
    | EthereumRlp.Item.List hashes => sequence (List.map (fixed_uint 32) hashes)
    | _ => None
    end.

  (** Match geth's protected-v classification, including the uint64 subtraction
      in deriveChainId for small invalid v values. Sender checks chain ID before
      signature scalars. Unprotected 0/1 remain invalid recovery identifiers. *)
  Definition legacy_chain_id (v : Z) : option Z :=
    if (v =? 27) || (v =? 28) || (v =? 0) || (v =? 1) then None else
    Some (if v <? 2 ^ 64 then ((v - 35) mod (2 ^ 64)) / 2 else (v - 35) / 2).

  Definition legacy_parity (v : Z) : Z :=
    match legacy_chain_id v with
    | Some chain_id => v - 2 * chain_id - 35
    | None => v - 27
    end.

  Module Envelope.
    Record t : Set := {
      transaction : TransactionAccounting.Transaction.t;
      v : Z;
      r : Z;
      s : Z;
      parity : Z;
      signing_payload : list Z;
    }.
  End Envelope.

  Definition field_count (tx_type : Z) : nat :=
    if tx_type =? 0 then 9%nat else
    if tx_type =? 1 then 11%nat else
    if tx_type =? 2 then 12%nat else 14%nat.

  Definition decode_fields (tx_type : Z) (fields : list EthereumRlp.Item.t) :
      option Envelope.t :=
    if negb (Nat.eqb (List.length fields) (field_count tx_type)) then None else
    let field_at := fun index => List.nth index fields (EthereumRlp.Item.Bytes []) in
    let typed := negb (tx_type =? 0) in
    let dynamic := (tx_type =? 2) || (tx_type =? 3) in
    let price_index := if tx_type =? 0 then 1%nat else
      if tx_type =? 1 then 2%nat else 3%nat in
    let gas_index := S price_index in
    let unsigned_count := (field_count tx_type - 3)%nat in
    let optional_field := fun (condition : bool) (index : nat) =>
      if condition then field_at index else EthereumRlp.Item.Bytes [] in
    match sequence (List.map uint
      [field_at (if typed then 1%nat else 0%nat); field_at gas_index; field_at price_index;
       optional_field dynamic 2%nat; field_at (gas_index + 2)%nat;
       field_at unsigned_count; field_at (unsigned_count + 1)%nat; field_at (unsigned_count + 2)%nat;
       optional_field typed 0%nat; optional_field (tx_type =? 3) 9%nat]),
      target (field_at (S gas_index)), bytes (field_at (gas_index + 3)%nat),
      access_list (if typed then field_at (gas_index + 4)%nat else EthereumRlp.Item.List []),
      blob_hashes (if tx_type =? 3 then field_at 10%nat else EthereumRlp.Item.List []) with
    | Some [nonce; gas; price; priority; value; v; r; s; typed_chain_id; blob_fee],
        Some target, Some data, Some access_list, Some blob_hashes =>
        if (2 ^ 64 <=? nonce) || (2 ^ 64 <=? gas) then None else
        if (tx_type =? 3) &&
          (List.existsb (fun value => 2 ^ 256 <=? value)
            [typed_chain_id; price; priority; value; blob_fee; v; r; s] ||
           match target with None => true | Some _ => false end) then None else
        let chain_id := if typed then Some typed_chain_id else legacy_chain_id v in
        let unsigned_fields := List.firstn unsigned_count fields in
        let signing_fields := if typed then unsigned_fields else
          match chain_id with
          | None => unsigned_fields
          | Some chain_id => unsigned_fields ++
              [EthereumRlp.Item.Bytes (EthereumRlp.big_endian chain_id);
               EthereumRlp.Item.Bytes []; EthereumRlp.Item.Bytes []]
          end in
        Some {| Envelope.transaction := {|
          TransactionAccounting.Transaction.tx_type := tx_type;
          TransactionAccounting.Transaction.caller := 0;
          TransactionAccounting.Transaction.target := target;
          TransactionAccounting.Transaction.nonce := nonce;
          TransactionAccounting.Transaction.chain_id := chain_id;
          TransactionAccounting.Transaction.gas_limit := gas;
          TransactionAccounting.Transaction.gas_price := price;
          TransactionAccounting.Transaction.max_priority_fee := if dynamic then Some priority else None;
          TransactionAccounting.Transaction.access_list := access_list;
          TransactionAccounting.Transaction.max_fee_per_blob_gas := blob_fee;
          TransactionAccounting.Transaction.blob_hashes := blob_hashes;
          TransactionAccounting.Transaction.value := value;
          TransactionAccounting.Transaction.data := data;
        |};
        Envelope.v := v;
        Envelope.r := r;
        Envelope.s := s;
        Envelope.parity := if typed then v else legacy_parity v;
        Envelope.signing_payload :=
          (if typed then [tx_type] else []) ++
          EthereumRlp.encode (EthereumRlp.Item.List signing_fields);
        |}
    | _, _, _, _, _ => None
    end.

  Module Error.
    Inductive t : Set :=
    | MalformedRlp
    | MalformedFields
    | InvalidSignature
    | TransactionTypeNotSupported (tx_type : Z)
    | RecoveryFailed
    | ChainIdMismatch (have expected : Z)
    | SenderMismatch (have expected : Z).
  End Error.

  Module Unsupported.
    Inductive t : Set :=
    | TransactionType (tx_type : Z)
    | BlobSidecar.
  End Unsupported.

  Module DecodeResult.
    Inductive t : Set :=
    | Decoded (envelope : Envelope.t)
    | Rejected (error : Error.t)
    | Unsupported (reason : Unsupported.t).
  End DecodeResult.

  Definition decode (input : list Z) : DecodeResult.t :=
    if negb (List.forallb EthereumRlpDecode.byte_valid input) then
      DecodeResult.Rejected Error.MalformedRlp else
    match input with
    | [] => DecodeResult.Rejected Error.MalformedRlp
    | first :: rest =>
        let typed := first <? 128 in
        let tx_type := if typed then first else 0 in
        if (typed && (tx_type =? 0)) || negb ((tx_type =? 0) || (tx_type =? 1) || (tx_type =? 2) || (tx_type =? 3)) then
          DecodeResult.Unsupported (Unsupported.TransactionType tx_type) else
        match EthereumRlpDecode.decode (if typed then rest else input) with
        | Some (EthereumRlp.Item.List fields) =>
            if (tx_type =? 3) && Nat.eqb (List.length fields) 4 then
              DecodeResult.Unsupported Unsupported.BlobSidecar else
            match decode_fields tx_type fields with
            | Some envelope => DecodeResult.Decoded envelope
            | None => DecodeResult.Rejected Error.MalformedFields
            end
        | Some _ => DecodeResult.Rejected Error.MalformedFields
        | None => DecodeResult.Rejected Error.MalformedRlp
        end
    end.

  Definition signature_valid_for_spec (spec : SpecId.t)
      (envelope : Envelope.t) : bool :=
    ((envelope.(Envelope.parity) =? 0) || (envelope.(Envelope.parity) =? 1)) &&
    Secp256k1.scalar_valid envelope.(Envelope.r) &&
    Secp256k1.scalar_valid envelope.(Envelope.s) &&
    (negb (TransactionAccounting.fork_enabled spec SpecId.HOMESTEAD) ||
      (envelope.(Envelope.s) <=? Secp256k1.scalar_modulus / 2)).

  Definition signature_valid (envelope : Envelope.t) : bool :=
    signature_valid_for_spec SpecId.CANCUN envelope.

  Definition signing_hash (envelope : Envelope.t) : Z :=
    Modexp.decode_be (Keccak256.hash envelope.(Envelope.signing_payload)).

  Definition with_caller (tx : TransactionAccounting.Transaction.t) (caller : Z) := {|
    TransactionAccounting.Transaction.tx_type := tx.(TransactionAccounting.Transaction.tx_type);
    TransactionAccounting.Transaction.caller := caller;
    TransactionAccounting.Transaction.target := tx.(TransactionAccounting.Transaction.target);
    TransactionAccounting.Transaction.nonce := tx.(TransactionAccounting.Transaction.nonce);
    TransactionAccounting.Transaction.chain_id := tx.(TransactionAccounting.Transaction.chain_id);
    TransactionAccounting.Transaction.gas_limit := tx.(TransactionAccounting.Transaction.gas_limit);
    TransactionAccounting.Transaction.gas_price := tx.(TransactionAccounting.Transaction.gas_price);
    TransactionAccounting.Transaction.max_priority_fee := tx.(TransactionAccounting.Transaction.max_priority_fee);
    TransactionAccounting.Transaction.access_list := tx.(TransactionAccounting.Transaction.access_list);
    TransactionAccounting.Transaction.max_fee_per_blob_gas := tx.(TransactionAccounting.Transaction.max_fee_per_blob_gas);
    TransactionAccounting.Transaction.blob_hashes := tx.(TransactionAccounting.Transaction.blob_hashes);
    TransactionAccounting.Transaction.value := tx.(TransactionAccounting.Transaction.value);
    TransactionAccounting.Transaction.data := tx.(TransactionAccounting.Transaction.data);
  |}.

  Module Result.
    Inductive t : Set :=
    | Authenticated (transaction : TransactionAccounting.Transaction.t)
    | Rejected (error : Error.t)
    | Unsupported (reason : Unsupported.t).
  End Result.

  Definition authenticate_for_spec (spec : SpecId.t) (chain_id : Z)
      (declared_sender : option Z)
      (input : list Z) : Result.t :=
    match decode input with
    | DecodeResult.Rejected error => Result.Rejected error
    | DecodeResult.Unsupported reason => Result.Unsupported reason
    | DecodeResult.Decoded envelope =>
        let tx := envelope.(Envelope.transaction) in
        if negb (TransactionAccounting.transaction_type_enabled spec
          tx.(TransactionAccounting.Transaction.tx_type)) then
          Result.Rejected (Error.TransactionTypeNotSupported
            tx.(TransactionAccounting.Transaction.tx_type)) else
        (* Frontier/Homestead signers use only v=27/28, even when protected-v
           decoding identifies a chain ID. Reject before testing chain ID. *)
        if (tx.(TransactionAccounting.Transaction.tx_type) =? 0) &&
          negb (TransactionAccounting.fork_enabled spec SpecId.SPURIOUS_DRAGON) &&
          (match tx.(TransactionAccounting.Transaction.chain_id) with
           | Some _ => true | None => false end) then
          Result.Rejected Error.InvalidSignature else
        let chain_matches := match tx.(TransactionAccounting.Transaction.chain_id) with
          | None => true
          | Some have => have =? chain_id
          end in
        if negb chain_matches then
          Result.Rejected (Error.ChainIdMismatch
            (match tx.(TransactionAccounting.Transaction.chain_id) with
             | Some have => have | None => 0 end) chain_id) else
        if negb (signature_valid_for_spec spec envelope) then Result.Rejected Error.InvalidSignature else
        match Secp256k1.recover (signing_hash envelope)
          envelope.(Envelope.r) envelope.(Envelope.s) envelope.(Envelope.parity) with
        | None => Result.Rejected Error.RecoveryFailed
        | Some bytes =>
            let sender := Modexp.decode_be bytes in
            match declared_sender with
            | Some expected =>
                if sender =? expected then Result.Authenticated (with_caller tx sender)
                else Result.Rejected (Error.SenderMismatch sender expected)
            | None => Result.Authenticated (with_caller tx sender)
            end
        end
    end.
  (** Preserve the original modern authentication API for existing callers.
      Execution bridges must use authenticate_for_spec with the selected fork. *)
  Definition authenticate (chain_id : Z) (declared_sender : option Z)
      (input : list Z) : Result.t :=
    authenticate_for_spec SpecId.CANCUN chain_id declared_sender input.
End TransactionAuth.
