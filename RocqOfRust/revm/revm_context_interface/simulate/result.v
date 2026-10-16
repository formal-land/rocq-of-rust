Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.

(** The payment and environment-validation subset of result.rs. *)
Module InvalidTransaction.
  Inductive t : Set :=
  | OverflowPaymentInTransaction
  | LackOfFundForMaxFee (fee balance : aliases.U256.t)
  | GasPriceLessThanBasefee
  | PriorityFeeGreaterThanMaxFee
  | InvalidChainId
  | MissingChainId
  | TxGasLimitGreaterThanCap (gas_limit cap : u64)
  | Eip2930NotSupported
  | Eip1559NotSupported
  | Eip4844NotSupported
  | Eip7702NotSupported
  | BlobGasPriceGreaterThanMax (block_blob_gas_price tx_max_fee_per_blob_gas : u128)
  | EmptyBlobs
  | BlobVersionNotSupported
  | TooManyBlobs (have max : usize)
  | EmptyAuthorizationList
  | CallerGasLimitMoreThanBlock
  | CreateInitCodeSizeLimit.
End InvalidTransaction.

Module InvalidHeader.
  Inductive t : Set :=
  | PrevrandaoNotSet
  | ExcessBlobGasNotSet.
End InvalidHeader.
