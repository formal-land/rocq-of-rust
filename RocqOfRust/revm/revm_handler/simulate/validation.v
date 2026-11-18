Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.links.common.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import core.links.result.
Require Import lib.simulate.lib.
Require Import revm.revm_context_interface.simulate.result.
Require Import revm.revm_context_interface.simulate.transaction.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.

(** Executable environment checks from validation.rs. These typed projections
    supply the current ContextTr getters without extending the older linked
    interfaces. Scalars, byte arrays and lengths satisfy Rust validity bounds.
    This subset does not establish a native ContextTr correspondence proof. *)
Module validation.
  Module TxFields.
    Record t : Set := {
      chain_id : option u64;
      kind : TxKind.t;
      input_length : usize;
      authorization_list_len : usize;
    }.
  End TxFields.

  Module BlockFields.
    Record t : Set := {
      basefee : u64;
      gas_limit : u64;
      blob_gasprice : u128;
      prevrandao : option aliases.B256.t;
      blob_excess_gas : option u64;
    }.
  End BlockFields.

  Module CfgFields.
    Record t : Set := {
      chain_id : u64;
      tx_chain_id_check : bool;
      tx_gas_limit_cap : u64;
      is_base_fee_check_disabled : bool;
      is_priority_fee_check_disabled : bool;
      is_block_gas_limit_disabled : bool;
      max_blobs_per_tx : option u64;
      max_initcode_size : usize;
    }.
  End CfgFields.

  Module EnvironmentError.
    Inductive t : Set :=
    | Header (error : InvalidHeader.t)
    | Transaction (error : InvalidTransaction.t).
  End EnvironmentError.

  Definition validate_header (spec : SpecId.t) (block : BlockFields.t)
      : Result.t unit InvalidHeader.t :=
    if Impl_SpecId.is_enabled_in spec SpecId.MERGE &&
      (match block.(BlockFields.prevrandao) with None => true | Some _ => false end)
    then Result.Err InvalidHeader.PrevrandaoNotSet
    else if Impl_SpecId.is_enabled_in spec SpecId.CANCUN &&
      (match block.(BlockFields.blob_excess_gas) with None => true | Some _ => false end)
    then Result.Err InvalidHeader.ExcessBlobGasNotSet
    else Result.Ok tt.

  Definition validate_legacy_gas_price (gas_price : u128) (base_fee : option u128)
      : Result.t unit InvalidTransaction.t :=
    match base_fee with
    | Some base_fee =>
      if gas_price <i base_fee then Result.Err InvalidTransaction.GasPriceLessThanBasefee
      else Result.Ok tt
    | None => Result.Ok tt
    end.

  Definition validate_priority_fee_tx (max_fee max_priority_fee : u128)
      (base_fee : option u128) (disable_priority_fee_check : bool)
      : Result.t unit InvalidTransaction.t :=
    if negb disable_priority_fee_check && (max_fee <i max_priority_fee)
    then Result.Err InvalidTransaction.PriorityFeeGreaterThanMaxFee
    else match base_fee with
    | Some base_fee =>
      let price := base_fee +is max_priority_fee in
      let effective_gas_price := if max_fee <i price then max_fee else price in
      if effective_gas_price <i base_fee
      then Result.Err InvalidTransaction.GasPriceLessThanBasefee
      else Result.Ok tt
    | None => Result.Ok tt
    end.

  Definition validate_eip4844_tx (blobs : list aliases.B256.t)
      (max_blob_fee block_blob_gas_price : u128) (max_blobs : option u64)
      : Result.t unit InvalidTransaction.t :=
    if max_blob_fee <i block_blob_gas_price
    then Result.Err (InvalidTransaction.BlobGasPriceGreaterThanMax
      block_blob_gas_price max_blob_fee)
    else match blobs with
    | nil => Result.Err InvalidTransaction.EmptyBlobs
    | _ =>
      if negb (List.forallb (fun blob => (FixedBytes.to_Z blob / 2 ^ 248 =? 1)%Z) blobs)
      then Result.Err InvalidTransaction.BlobVersionNotSupported
      else match max_blobs with
      | None => Result.Ok tt
      | Some max_blobs =>
        let have : usize := {| Integer.value := Z.of_nat (List.length blobs) |} in
        let maximum : usize := {| Integer.value := max_blobs.(Integer.value) |} in
        if maximum <i have then Result.Err (InvalidTransaction.TooManyBlobs have maximum)
        else Result.Ok tt
      end
    end.

  Definition validate_chain_id (tx_type : u8) (chain_id : option u64)
      (cfg : CfgFields.t) : Result.t unit InvalidTransaction.t :=
    if negb cfg.(CfgFields.tx_chain_id_check) then Result.Ok tt else
    match chain_id with
    | Some chain_id =>
      if BinOp.eq chain_id cfg.(CfgFields.chain_id) then Result.Ok tt
      else Result.Err InvalidTransaction.InvalidChainId
    | None =>
      if (1 <=? tx_type.(Integer.value))%Z && (tx_type.(Integer.value) <=? 4)%Z
      then Result.Err InvalidTransaction.MissingChainId
      else Result.Ok tt
    end.

  (** This phase and validate_tx_limits split validate_tx_env so fixture-only
      encoding restrictions can keep their existing error precedence. *)
  Definition validate_tx_type {Tx : Set} `{Transaction.Fees.C Tx}
      (tx : Tx) (extra : TxFields.t) (cfg : CfgFields.t) (block : BlockFields.t)
      (spec : SpecId.t) : Result.t unit InvalidTransaction.t :=
    if cfg.(CfgFields.tx_gas_limit_cap) <i Transaction.Fees.gas_limit tx
    then Result.Err (InvalidTransaction.TxGasLimitGreaterThanCap
      (Transaction.Fees.gas_limit tx) cfg.(CfgFields.tx_gas_limit_cap))
    else
      let base_fee := if cfg.(CfgFields.is_base_fee_check_disabled) then None
        else Some ({| Integer.value := block.(BlockFields.basefee).(Integer.value) |} : u128) in
      let priority := match Transaction.Fees.max_priority_fee_per_gas tx with
        | Some priority => priority | None => {| Integer.value := 0 |} end in
      let check_priority := fun _ : unit => validate_priority_fee_tx
        (Transaction.Fees.max_fee_per_gas tx) priority base_fee
        cfg.(CfgFields.is_priority_fee_check_disabled) in
      let tx_type := (Transaction.Fees.tx_type tx).(Integer.value) in
      if Z.eqb tx_type 0 then validate_legacy_gas_price (Transaction.Fees.gas_price tx) base_fee
      else if Z.eqb tx_type 1 then
        if negb (Impl_SpecId.is_enabled_in spec SpecId.BERLIN)
        then Result.Err InvalidTransaction.Eip2930NotSupported
        else validate_legacy_gas_price (Transaction.Fees.gas_price tx) base_fee
      else if Z.eqb tx_type 2 then
        if negb (Impl_SpecId.is_enabled_in spec SpecId.LONDON)
        then Result.Err InvalidTransaction.Eip1559NotSupported
        else check_priority tt
      else if Z.eqb tx_type 3 then
        if negb (Impl_SpecId.is_enabled_in spec SpecId.CANCUN)
        then Result.Err InvalidTransaction.Eip4844NotSupported
        else match check_priority tt with
        | Result.Err error => Result.Err error
        | Result.Ok _ => validate_eip4844_tx
          (Transaction.Fees.blob_versioned_hashes tx)
          (Transaction.Fees.max_fee_per_blob_gas tx) block.(BlockFields.blob_gasprice)
          cfg.(CfgFields.max_blobs_per_tx)
        end
      else if Z.eqb tx_type 4 then
        if negb (Impl_SpecId.is_enabled_in spec SpecId.PRAGUE)
        then Result.Err InvalidTransaction.Eip7702NotSupported
        else match check_priority tt with
        | Result.Err error => Result.Err error
        | Result.Ok _ =>
          if BinOp.eq extra.(TxFields.authorization_list_len) {| Integer.value := 0 |}
          then Result.Err InvalidTransaction.EmptyAuthorizationList
          else Result.Ok tt
        end
      else Result.Ok tt.

  Definition validate_tx_limits {Tx : Set} `{Transaction.Fees.C Tx}
      (tx : Tx) (extra : TxFields.t) (cfg : CfgFields.t) (block : BlockFields.t)
      (spec : SpecId.t) : Result.t unit InvalidTransaction.t :=
    if negb cfg.(CfgFields.is_block_gas_limit_disabled) &&
      (block.(BlockFields.gas_limit) <i Transaction.Fees.gas_limit tx)
    then Result.Err InvalidTransaction.CallerGasLimitMoreThanBlock
    else if Impl_SpecId.is_enabled_in spec SpecId.SHANGHAI &&
      (match extra.(TxFields.kind) with TxKind.Create => true | TxKind.Call _ => false end) &&
      (cfg.(CfgFields.max_initcode_size) <i extra.(TxFields.input_length))
    then Result.Err InvalidTransaction.CreateInitCodeSizeLimit
    else Result.Ok tt.

  Definition validate_tx_env {Tx : Set} `{Transaction.Fees.C Tx}
      (tx : Tx) (extra : TxFields.t) (cfg : CfgFields.t) (block : BlockFields.t)
      (spec : SpecId.t) : Result.t unit InvalidTransaction.t :=
    match validate_chain_id (Transaction.Fees.tx_type tx) extra.(TxFields.chain_id) cfg with
    | Result.Err error => Result.Err error
    | Result.Ok _ =>
      match validate_tx_type tx extra cfg block spec with
      | Result.Err error => Result.Err error
      | Result.Ok _ => validate_tx_limits tx extra cfg block spec
      end
    end.

  Definition validate_env {Tx : Set} `{Transaction.Fees.C Tx}
      (tx : Tx) (extra : TxFields.t) (cfg : CfgFields.t) (block : BlockFields.t)
      (spec : SpecId.t) : Result.t unit EnvironmentError.t :=
    match validate_header spec block with
    | Result.Err error => Result.Err (EnvironmentError.Header error)
    | Result.Ok _ =>
      match validate_tx_env tx extra cfg block spec with
      | Result.Err error => Result.Err (EnvironmentError.Transaction error)
      | Result.Ok _ => Result.Ok tt
      end
    end.
End validation.
