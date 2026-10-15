From Stdlib Require Import Bool List ZArith.

Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_context_interface.simulate.transaction.
Require Import revm.revm_context_interface.simulate.result.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import core.links.result.
Require Import alloy_eip7702.simulate.auth_list.
Require Import lib.simulate.lib.
Require Import links.M.
Require Import ruint.links.lib.
Require Import alloy_primitives.bits.links.address.

Import ListNotations.
Open Scope Z_scope.

(** Standalone gas accounting from gas/calc.rs, handler.rs::last_frame_result
    and post_execution.rs. This module does not execute bytecode or validate
    signatures, sender nonce/balance, block headers or journal state. *)
Module TransactionAccounting.
  Module Transaction.
    Record t : Set := {
      tx_type : Z;
      caller : Z;
      target : option Z;
      nonce : Z;
      chain_id : option Z;
      gas_limit : Z;
      gas_price : Z;
      max_priority_fee : option Z;
      access_list : list (Z * list Z);
      authorization_list : list SignedAuthorization.t;
      max_fee_per_blob_gas : Z;
      blob_hashes : list Z;
      value : Z;
      data : list Z;
    }.
  End Transaction.

  #[export] Instance fee_fields : transaction.Transaction.Fees.C Transaction.t := {
    transaction.Transaction.Fees.tx_type tx := {| Integer.value := tx.(Transaction.tx_type) |};
    transaction.Transaction.Fees.gas_limit tx := {| Integer.value := tx.(Transaction.gas_limit) |};
    transaction.Transaction.Fees.value tx := {| Uint.value := tx.(Transaction.value) |};
    transaction.Transaction.Fees.gas_price tx := {| Integer.value := tx.(Transaction.gas_price) |};
    transaction.Transaction.Fees.blob_versioned_hashes tx :=
      List.map FixedBytes.from_Z tx.(Transaction.blob_hashes);
    transaction.Transaction.Fees.max_fee_per_blob_gas tx :=
      {| Integer.value := tx.(Transaction.max_fee_per_blob_gas) |};
    transaction.Transaction.Fees.max_priority_fee_per_gas tx :=
      option_map (fun priority => {| Integer.value := priority |}) tx.(Transaction.max_priority_fee);
  }.

  Module Block.
    Record t : Set := {
      gas_limit : Z;
      base_fee : Z;
      blob_base_fee : Z;
    }.
  End Block.

  Module UnsupportedReason.
    Inductive t : Set :=
    | Fork (spec : SpecId.t)
    | TransactionType (tx_type : Z)
    | Creation
    | GasArithmeticOverflow.
  End UnsupportedReason.

  Module MalformedReason.
    Inductive t : Set :=
    | TransactionFields
    | BlockFields
    | ConfigurationFields
    | FrameFields.
  End MalformedReason.

  Module GasError.
    Inductive t : Set :=
    | GasPriceBelowBaseFee
    | Eip2930NotSupported
    | Eip1559NotSupported
    | Eip7702NotSupported
    | EmptyAuthorizationList
    | AuthorizationCreate
    | Eip4844NotSupported
    | PriorityFeeGreaterThanMaxFee
    | CreateInitCodeSizeLimit
    | BlobGasPriceGreaterThanMax (block_price maximum_price : Z)
    | EmptyBlobs
    | BlobVersionNotSupported
    | TooManyBlobs (have maximum : Z)
    | GasLimitAboveBlock
    | GasLimitAboveCap (available cap : Z)
    | IntrinsicGasTooHigh (required available : Z)
    | FloorGasTooHigh (required available : Z)
    | PaymentOverflow.
  End GasError.

  Module Result.
    Inductive t (A : Set) : Set :=
    | Ready (value : A)
    | Unsupported (reason : UnsupportedReason.t)
    | Malformed (reason : MalformedReason.t)
    | Rejected (reason : GasError.t).

    Arguments Ready {A}.
    Arguments Unsupported {A}.
    Arguments Malformed {A}.
    Arguments Rejected {A}.
  End Result.

  Module InitialGas.
    Record t : Set := {
      intrinsic : Z;
      floor : Z;
      execution : Z;
      upfront_fee : Z;
    }.
  End InitialGas.

  Module FrameStatus.
    Inductive t : Set := Success | Revert | Halt.
  End FrameStatus.

  Module FrameGas.
    Record t : Set := {
      status : FrameStatus.t;
      remaining : Z;
      refunded : Z;
    }.
  End FrameGas.

  Module Settlement.
    Record t : Set := {
      gas_remaining : Z;
      gas_refunded : Z;
      gas_used : Z;
      caller_reimbursement : Z;
      beneficiary_reward : Z;
      base_fee_burn : Z;
      blob_fee_burn : Z;
    }.
  End Settlement.

  Definition bounded (bits value : Z) : bool :=
    (0 <=? value) && (value <? 2 ^ bits).

  Definition authorization_fields_valid (authorization : SignedAuthorization.t) : bool :=
    let inner := authorization.(SignedAuthorization.inner) in
    bounded 256 inner.(Authorization.chain_id).(Uint.value) &&
    bounded 160 inner.(Authorization.address).(Address.value) &&
    bounded 64 inner.(Authorization.nonce).(Integer.value) &&
    bounded 8 authorization.(SignedAuthorization.y_parity).(Integer.value) &&
    bounded 256 authorization.(SignedAuthorization.r).(Uint.value) &&
    bounded 256 authorization.(SignedAuthorization.s).(Uint.value).

  Definition transaction_fields_valid (tx : Transaction.t) : bool :=
    bounded 8 tx.(Transaction.tx_type) &&
    bounded 160 tx.(Transaction.caller) &&
    (match tx.(Transaction.target) with
     | Some target => bounded 160 target
     | None => true
     end) &&
    bounded 64 tx.(Transaction.nonce) &&
    (match tx.(Transaction.chain_id) with
     | Some chain_id => bounded 64 chain_id
     | None => true
     end) &&
    bounded 64 tx.(Transaction.gas_limit) &&
    bounded 128 tx.(Transaction.gas_price) &&
    (match tx.(Transaction.max_priority_fee) with
     | Some priority => bounded 128 priority
     | None => true
     end) &&
    List.forallb (fun entry => bounded 160 (fst entry) &&
      List.forallb (bounded 256) (snd entry)) tx.(Transaction.access_list) &&
    List.forallb authorization_fields_valid tx.(Transaction.authorization_list) &&
    bounded 128 tx.(Transaction.max_fee_per_blob_gas) &&
    List.forallb (bounded 256) tx.(Transaction.blob_hashes) &&
    bounded 256 tx.(Transaction.value) &&
    List.forallb (bounded 8) tx.(Transaction.data).

  Definition block_fields_valid (block : Block.t) : bool :=
    bounded 64 block.(Block.gas_limit) && bounded 64 block.(Block.base_fee) &&
    bounded 128 block.(Block.blob_base_fee).

  Definition blob_limit_valid (limit : option Z) : bool :=
    match limit with Some maximum => bounded 64 maximum | None => true end.

  Definition accounting_fork_supported (spec : SpecId.t) : bool :=
    match spec with
    | SpecId.FRONTIER | SpecId.HOMESTEAD | SpecId.TANGERINE
    | SpecId.SPURIOUS_DRAGON | SpecId.BYZANTIUM | SpecId.PETERSBURG
    | SpecId.ISTANBUL | SpecId.BERLIN | SpecId.LONDON | SpecId.MERGE
    | SpecId.SHANGHAI | SpecId.CANCUN | SpecId.PRAGUE | SpecId.OSAKA => true
    | _ => false
    end.

  Definition fork_enabled (spec activation : SpecId.t) : bool :=
    SpecId.get_discriminant activation <=? SpecId.get_discriminant spec.

  (** Shared activation rule for signed envelopes and normalized TxEnv inputs. *)
  Definition transaction_type_enabled (spec : SpecId.t) (tx_type : Z) : bool :=
    if tx_type =? 0 then true else
    if tx_type =? 1 then fork_enabled spec SpecId.BERLIN else
    if tx_type =? 2 then fork_enabled spec SpecId.LONDON else
    if tx_type =? 3 then fork_enabled spec SpecId.CANCUN else
    if tx_type =? 4 then fork_enabled spec SpecId.PRAGUE else false.

  Definition calldata_tokens (spec : SpecId.t) (data : list Z) : Z :=
    let nonzero_multiplier := if fork_enabled spec SpecId.ISTANBUL then 4 else 17 in
    List.fold_left (fun tokens byte =>
      tokens + (if byte =? 0 then 1 else nonzero_multiplier)) data 0.

  Definition effective_gas_price (tx : Transaction.t) (base_fee : Z) : Z :=
    (transaction.Transaction.Fees.effective_gas_price tx
      {| Integer.value := base_fee |}).(Integer.value).

  Definition total_blob_gas (tx : Transaction.t) : Z :=
    (transaction.Transaction.Fees.total_blob_gas tx).(Integer.value).

  Definition blob_fee (tx : Transaction.t) (price : Z) : Z :=
    if tx.(Transaction.tx_type) =? 3 then
      (BinOp.Saturating.mul
        ({| Integer.value := total_blob_gas tx |} : u128)
        {| Integer.value := price |}).(Integer.value)
    else 0.

  Definition maximum_payment (tx : Transaction.t)
      : core.links.result.Result.t Z InvalidTransaction.t :=
    match transaction.Transaction.Fees.max_balance_spending tx with
    | core.links.result.Result.Ok amount => core.links.result.Result.Ok amount.(Uint.value)
    | core.links.result.Result.Err error => core.links.result.Result.Err error
    end.

  Definition access_list_gas (tx : Transaction.t) : Z :=
    if tx.(Transaction.tx_type) =? 0 then 0 else
    List.fold_left (fun gas entry =>
      gas + 2400 + 1900 * Z.of_nat (List.length (snd entry)))
      tx.(Transaction.access_list) 0.

  Definition authorization_list_gas (tx : Transaction.t) : Z :=
    if tx.(Transaction.tx_type) =? 4 then
      25000 * Z.of_nat (List.length tx.(Transaction.authorization_list)) else 0.

  Definition prepare_gas_with_blob_limit (spec : SpecId.t) (tx : Transaction.t)
      (block : Block.t) (max_blobs : option Z) :
      Result.t InitialGas.t :=
    if negb (accounting_fork_supported spec) then
      Result.Unsupported (UnsupportedReason.Fork spec)
    else
      if negb (transaction_fields_valid tx) then
        Result.Malformed MalformedReason.TransactionFields
      else if negb (block_fields_valid block) then
        Result.Malformed MalformedReason.BlockFields
      else if negb (blob_limit_valid max_blobs) then
        Result.Malformed MalformedReason.ConfigurationFields
      else if negb ((tx.(Transaction.tx_type) =? 0) ||
        (tx.(Transaction.tx_type) =? 1) || (tx.(Transaction.tx_type) =? 2) ||
        (tx.(Transaction.tx_type) =? 3) || (tx.(Transaction.tx_type) =? 4)) then
        Result.Unsupported (UnsupportedReason.TransactionType tx.(Transaction.tx_type))
      else
        if fork_enabled spec SpecId.OSAKA &&
          (16777216 <? tx.(Transaction.gas_limit)) then
          Result.Rejected (GasError.GasLimitAboveCap tx.(Transaction.gas_limit) 16777216)
        else if (tx.(Transaction.tx_type) =? 1) &&
          negb (transaction_type_enabled spec tx.(Transaction.tx_type)) then
          Result.Rejected GasError.Eip2930NotSupported
        else if (tx.(Transaction.tx_type) =? 2) &&
          negb (transaction_type_enabled spec tx.(Transaction.tx_type)) then
          Result.Rejected GasError.Eip1559NotSupported
        else if (tx.(Transaction.tx_type) =? 3) &&
          negb (transaction_type_enabled spec tx.(Transaction.tx_type)) then
          Result.Rejected GasError.Eip4844NotSupported
        else if (tx.(Transaction.tx_type) =? 4) &&
          negb (transaction_type_enabled spec tx.(Transaction.tx_type)) then
          Result.Rejected GasError.Eip7702NotSupported
        else if ((tx.(Transaction.tx_type) =? 2) || (tx.(Transaction.tx_type) =? 3) || (tx.(Transaction.tx_type) =? 4)) &&
          (match tx.(Transaction.max_priority_fee) with
           | Some priority => tx.(Transaction.gas_price) <? priority
           | None => false
           end) then
          Result.Rejected GasError.PriorityFeeGreaterThanMaxFee
        else if (if (tx.(Transaction.tx_type) =? 2) || (tx.(Transaction.tx_type) =? 3) || (tx.(Transaction.tx_type) =? 4) then
          Z.min tx.(Transaction.gas_price)
            (Z.min (2 ^ 128 - 1) (block.(Block.base_fee) +
              match tx.(Transaction.max_priority_fee) with
              | Some priority => priority | None => 0 end))
          else tx.(Transaction.gas_price)) <? block.(Block.base_fee) then
          Result.Rejected GasError.GasPriceBelowBaseFee
        else if (tx.(Transaction.tx_type) =? 4) &&
          Nat.eqb (List.length tx.(Transaction.authorization_list)) 0 then
          Result.Rejected GasError.EmptyAuthorizationList
        else if (tx.(Transaction.tx_type) =? 4) &&
          (match tx.(Transaction.target) with None => true | Some _ => false end) then
          Result.Rejected GasError.AuthorizationCreate
        else if (tx.(Transaction.tx_type) =? 3) &&
          (tx.(Transaction.max_fee_per_blob_gas) <? block.(Block.blob_base_fee)) then
          Result.Rejected (GasError.BlobGasPriceGreaterThanMax
            block.(Block.blob_base_fee) tx.(Transaction.max_fee_per_blob_gas))
        else if (tx.(Transaction.tx_type) =? 3) &&
          Nat.eqb (List.length tx.(Transaction.blob_hashes)) 0 then
          Result.Rejected GasError.EmptyBlobs
        else if (tx.(Transaction.tx_type) =? 3) && negb
          (List.forallb (fun hash => hash / 2 ^ 248 =? 1) tx.(Transaction.blob_hashes)) then
          Result.Rejected GasError.BlobVersionNotSupported
        else if (tx.(Transaction.tx_type) =? 3) &&
          (match max_blobs with
           | Some maximum => maximum <? Z.of_nat (List.length tx.(Transaction.blob_hashes))
           | None => false
           end) then
          Result.Rejected (GasError.TooManyBlobs
            (Z.of_nat (List.length tx.(Transaction.blob_hashes)))
            (match max_blobs with Some maximum => maximum | None => 0 end))
        else if block.(Block.gas_limit) <? tx.(Transaction.gas_limit) then
          Result.Rejected GasError.GasLimitAboveBlock
        else if fork_enabled spec SpecId.SHANGHAI &&
          (match tx.(Transaction.target) with
          | None => 49152 <? Z.of_nat (List.length tx.(Transaction.data))
          | Some _ => false
          end) then Result.Rejected GasError.CreateInitCodeSizeLimit
        else
          let tokens := calldata_tokens spec tx.(Transaction.data) in
          let creation := match tx.(Transaction.target) with
            | None => (if fork_enabled spec SpecId.HOMESTEAD then 32000 else 0) +
                (if fork_enabled spec SpecId.SHANGHAI then
                  2 * ((Z.of_nat (List.length tx.(Transaction.data)) + 31) / 32)
                else 0)
            | Some _ => 0
            end in
          let intrinsic := 21000 + 4 * tokens + access_list_gas tx + creation +
            authorization_list_gas tx in
          let floor := if fork_enabled spec SpecId.PRAGUE then
            21000 + 10 * tokens else 0 in
          if negb (bounded 64 tokens && bounded 64 intrinsic && bounded 64 floor) then
            Result.Unsupported UnsupportedReason.GasArithmeticOverflow
          else if tx.(Transaction.gas_limit) <? intrinsic then
            Result.Rejected (GasError.IntrinsicGasTooHigh intrinsic tx.(Transaction.gas_limit))
          else if tx.(Transaction.gas_limit) <? floor then
            Result.Rejected (GasError.FloorGasTooHigh floor tx.(Transaction.gas_limit))
          else
            let upfront_fee := tx.(Transaction.gas_limit) *
              effective_gas_price tx block.(Block.base_fee) +
              blob_fee tx block.(Block.blob_base_fee) in
            Result.Ready {|
              InitialGas.intrinsic := intrinsic;
              InitialGas.floor := floor;
              InitialGas.execution := tx.(Transaction.gas_limit) - intrinsic;
              InitialGas.upfront_fee := upfront_fee;
            |}.

  Definition prepare_gas (spec : SpecId.t) (tx : Transaction.t) (block : Block.t) :
      Result.t InitialGas.t :=
    prepare_gas_with_blob_limit spec tx block None.

  Definition payment_valid (tx : Transaction.t) (initial : InitialGas.t) : bool :=
    match maximum_payment tx with
    | core.links.result.Result.Ok _ => bounded 256 initial.(InitialGas.upfront_fee)
    | core.links.result.Result.Err _ => false
    end.

  Definition prepare (spec : SpecId.t) (tx : Transaction.t) (block : Block.t) :
      Result.t InitialGas.t :=
    match prepare_gas spec tx block with
    | Result.Ready initial =>
      if payment_valid tx initial then Result.Ready initial
      else Result.Rejected GasError.PaymentOverflow
    | Result.Unsupported reason => Result.Unsupported reason
    | Result.Malformed reason => Result.Malformed reason
    | Result.Rejected reason => Result.Rejected reason
    end.

  Definition frame_fields_valid (initial : InitialGas.t) (frame : FrameGas.t) : bool :=
    (0 <=? frame.(FrameGas.remaining)) &&
    (frame.(FrameGas.remaining) <=? initial.(InitialGas.execution)) &&
    (- (2 ^ 63) <=? frame.(FrameGas.refunded)) &&
    (frame.(FrameGas.refunded) <? 2 ^ 63).

  (** The input frame gas is supplied by an execution layer. The signed refund
      cast matches Gas::set_final_refund, including its u64 cast; refund capping
      precedes the Prague/Osaka floor. No account balances are changed here. *)
  Definition settle_with_authorization_refund (authorization_refund : u64) (spec : SpecId.t) (tx : Transaction.t) (block : Block.t)
      (frame : FrameGas.t) : Result.t Settlement.t :=
    match prepare spec tx block with
    | Result.Unsupported reason => Result.Unsupported reason
    | Result.Malformed reason => Result.Malformed reason
    | Result.Rejected reason => Result.Rejected reason
    | Result.Ready initial =>
      if negb (frame_fields_valid initial frame) then
        Result.Malformed MalformedReason.FrameFields
      else
        let remaining := match frame.(FrameGas.status) with
          | FrameStatus.Success | FrameStatus.Revert => frame.(FrameGas.remaining)
          | FrameStatus.Halt => 0
          end in
        let spent := tx.(Transaction.gas_limit) - remaining in
        let raw_refund := match frame.(FrameGas.status) with
          | FrameStatus.Success => frame.(FrameGas.refunded)
          | _ => 0
          end in
        (* Rust casts the authorization refund to i64, adds it after clearing
           a failed frame's refund, then casts the final counter to u64. *)
        let raw_refund := (BinOp.Wrap.add
          ({| Integer.value := raw_refund mod 2 ^ 64 |} : u64)
          authorization_refund).(Integer.value) in
        let refund_quotient := if fork_enabled spec SpecId.LONDON then 5 else 2 in
        let refunded := Z.min (raw_refund mod 2 ^ 64) (spent / refund_quotient) in
        let '(remaining, refunded) :=
          if spent - refunded <? initial.(InitialGas.floor) then
            (Z.max 0 (tx.(Transaction.gas_limit) - initial.(InitialGas.floor)), 0)
          else (remaining, refunded) in
        let used := Z.max 0 (tx.(Transaction.gas_limit) - remaining - refunded) in
        let price := effective_gas_price tx block.(Block.base_fee) in
        let base_fee := if fork_enabled spec SpecId.LONDON then block.(Block.base_fee) else 0 in
        Result.Ready {|
          Settlement.gas_remaining := remaining;
          Settlement.gas_refunded := refunded;
          Settlement.gas_used := used;
          Settlement.caller_reimbursement :=
            Z.min (2 ^ 128 - 1) (price * (remaining + refunded));
          Settlement.beneficiary_reward :=
            Z.max 0 (price - base_fee) * used;
          Settlement.base_fee_burn := base_fee * used;
          Settlement.blob_fee_burn := blob_fee tx block.(Block.blob_base_fee);
        |}
    end.

  Definition settle (spec : SpecId.t) (tx : Transaction.t) (block : Block.t)
      (frame : FrameGas.t) : Result.t Settlement.t :=
    settle_with_authorization_refund {| Integer.value := 0 |} spec tx block frame.
End TransactionAccounting.
