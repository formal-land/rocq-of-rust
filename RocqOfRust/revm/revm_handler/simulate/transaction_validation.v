From Stdlib Require Import Bool List ZArith.

Require Import alloy_primitives.utils.simulate.keccak256.
Require Import revm.revm_handler.simulate.ethereum_rlp.
Require Import revm.revm_handler.simulate.ethereum_rlp_decode.
Require Import revm.revm_handler.simulate.transaction_accounting.
Require Import revm.revm_handler.simulate.transaction_auth.
Require Import revm.revm_primitives.links.hardfork.

Import ListNotations.
Open Scope Z_scope.

(** Raw transaction-test validation is independent of a block and account
    state. The full transaction runner performs those other checks separately. *)
Module TransactionValidation.
  Module Rejection.
    Inductive t : Set :=
    | MalformedEnvelope
    | InvalidSignature
    | EmptyAuthorizationList
    | IntrinsicGasTooHigh
    | FloorGasTooHigh
    | GasArithmeticOverflow.
  End Rejection.

  Module Unsupported.
    Inductive t : Set :=
    | TransactionType (tx_type : Z)
    | BlobSidecar
    | AuthorizationExecution.
  End Unsupported.

  Module Result.
    Inductive t : Set :=
    | Valid (sender : Z) (hash : list Z) (intrinsic_gas : Z)
    | Rejected (reason : Rejection.t)
    | Unsupported (reason : Unsupported.t).
  End Result.

  Definition checked_uint (bits : Z) (item : EthereumRlp.Item.t) : option Z :=
    match TransactionAuth.uint item with
    | Some value => if TransactionAccounting.bounded bits value then Some value else None
    | None => None
    end.

  Definition authorization (item : EthereumRlp.Item.t) : bool :=
    match item with
    | EthereumRlp.Item.List [chain; address; nonce; parity; r; s] =>
        match checked_uint 256 chain, TransactionAuth.fixed_uint 20 address,
          checked_uint 64 nonce, checked_uint 8 parity,
          checked_uint 256 r, checked_uint 256 s with
        | Some _, Some _, Some _, Some _, Some _, Some _ => true
        | _, _, _, _, _, _ => false
        end
    | _ => false
    end.

  Definition authorization_list (item : EthereumRlp.Item.t) : option (list EthereumRlp.Item.t) :=
    match item with
    | EthereumRlp.Item.List entries =>
        if List.forallb authorization entries then Some entries else None
    | _ => None
    end.

  Definition set_code_fields_valid (fields : list EthereumRlp.Item.t) : option bool :=
    match fields with
    | [chain; nonce; priority; fee; gas; to; value; data;
       access_list; authorizations; parity; r; s] =>
        match checked_uint 256 chain, checked_uint 64 nonce,
          checked_uint 256 priority, checked_uint 256 fee,
          checked_uint 64 gas, TransactionAuth.fixed_uint 20 to,
          checked_uint 256 value, TransactionAuth.bytes data,
          TransactionAuth.access_list access_list,
          authorization_list authorizations,
          checked_uint 256 parity, checked_uint 256 r, checked_uint 256 s with
        | Some _, Some _, Some _, Some _, Some _, Some _, Some _, Some _,
          Some _, Some entries, Some _, Some _, Some _ => Some (negb (Nat.eqb (List.length entries) 0))
        | _, _, _, _, _, _, _, _, _, _, _, _, _ => None
        end
    | _ => None
    end.

  Definition validate_set_code (raw : list Z) : Result.t :=
    match EthereumRlpDecode.decode (List.skipn 1 raw) with
    | Some (EthereumRlp.Item.List fields) =>
        match set_code_fields_valid fields with
        | None => Result.Rejected Rejection.MalformedEnvelope
        | Some false => Result.Rejected Rejection.EmptyAuthorizationList
        | Some true => Result.Unsupported Unsupported.AuthorizationExecution
        end
    | _ => Result.Rejected Rejection.MalformedEnvelope
    end.

  Definition intrinsic (spec : SpecId.t) (tx : TransactionAccounting.Transaction.t) : Z :=
    let tokens := TransactionAccounting.calldata_tokens spec tx.(TransactionAccounting.Transaction.data) in
    let creation := match tx.(TransactionAccounting.Transaction.target) with
      | None => (if TransactionAccounting.fork_enabled spec SpecId.HOMESTEAD then 32000 else 0) +
          (if TransactionAccounting.fork_enabled spec SpecId.SHANGHAI then
            2 * ((Z.of_nat (List.length tx.(TransactionAccounting.Transaction.data)) + 31) / 32)
           else 0)
      | Some _ => 0
      end in
    21000 + 4 * tokens + TransactionAccounting.access_list_gas tx + creation.

  Definition floor (spec : SpecId.t) (tx : TransactionAccounting.Transaction.t) : Z :=
    if TransactionAccounting.fork_enabled spec SpecId.PRAGUE then
      21000 + 10 * TransactionAccounting.calldata_tokens spec
        tx.(TransactionAccounting.Transaction.data)
    else 0.

  Definition validate (spec : SpecId.t) (chain_id : Z) (raw : list Z) : Result.t :=
    if negb (List.forallb EthereumRlpDecode.byte_valid raw) then
      Result.Rejected Rejection.MalformedEnvelope else
    if negb (TransactionAccounting.accounting_fork_supported spec) then
      Result.Unsupported (Unsupported.TransactionType (-1)) else
    match raw with
    | 4 :: _ =>
        if TransactionAccounting.fork_enabled spec SpecId.PRAGUE
        then validate_set_code raw
        else Result.Unsupported (Unsupported.TransactionType 4)
    | _ =>
        match TransactionAuth.decode raw with
        | TransactionAuth.DecodeResult.Unsupported (TransactionAuth.Unsupported.TransactionType tx_type) =>
            Result.Unsupported (Unsupported.TransactionType tx_type)
        | TransactionAuth.DecodeResult.Unsupported TransactionAuth.Unsupported.BlobSidecar =>
            Result.Unsupported Unsupported.BlobSidecar
        | TransactionAuth.DecodeResult.Rejected _ =>
            Result.Rejected Rejection.MalformedEnvelope
        | TransactionAuth.DecodeResult.Decoded envelope =>
            let tx := envelope.(TransactionAuth.Envelope.transaction) in
            if negb (TransactionAccounting.bounded 256 tx.(TransactionAccounting.Transaction.value))
            then Result.Rejected Rejection.MalformedEnvelope else
            match TransactionAuth.authenticate_for_spec spec chain_id None raw with
            | TransactionAuth.Result.Rejected _ => Result.Rejected Rejection.InvalidSignature
            | TransactionAuth.Result.Unsupported _ =>
                Result.Unsupported (Unsupported.TransactionType tx.(TransactionAccounting.Transaction.tx_type))
            | TransactionAuth.Result.Authenticated signed_tx =>
                let gas := intrinsic spec signed_tx in
                let floor_gas := floor spec signed_tx in
                if negb (TransactionAccounting.bounded 64 gas &&
                  TransactionAccounting.bounded 64 floor_gas) then
                  Result.Rejected Rejection.GasArithmeticOverflow else
                if signed_tx.(TransactionAccounting.Transaction.gas_limit) <? gas then
                  Result.Rejected Rejection.IntrinsicGasTooHigh else
                if signed_tx.(TransactionAccounting.Transaction.gas_limit) <? floor_gas then
                  Result.Rejected Rejection.FloorGasTooHigh else
                Result.Valid signed_tx.(TransactionAccounting.Transaction.caller)
                  (Keccak256.hash raw) gas
            end
        end
    end.
End TransactionValidation.
