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

  Definition intrinsic (spec : SpecId.t) (tx : TransactionAccounting.Transaction.t) : Z :=
    let tokens := TransactionAccounting.calldata_tokens spec tx.(TransactionAccounting.Transaction.data) in
    let creation := match tx.(TransactionAccounting.Transaction.target) with
      | None => (if TransactionAccounting.fork_enabled spec SpecId.HOMESTEAD then 32000 else 0) +
          (if TransactionAccounting.fork_enabled spec SpecId.SHANGHAI then
            2 * ((Z.of_nat (List.length tx.(TransactionAccounting.Transaction.data)) + 31) / 32)
           else 0)
      | Some _ => 0
      end in
    21000 + 4 * tokens + TransactionAccounting.access_list_gas tx + creation +
      TransactionAccounting.authorization_list_gas tx.

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
        if (tx.(TransactionAccounting.Transaction.tx_type) =? 4) &&
          Nat.eqb (List.length tx.(TransactionAccounting.Transaction.authorization_list)) 0 then
          Result.Rejected Rejection.EmptyAuthorizationList else
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
    end.
End TransactionValidation.
