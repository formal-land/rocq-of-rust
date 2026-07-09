Require Import links.RocqOfRust.

(*
pub struct BlobExcessGasAndPrice {
    pub excess_blob_gas: u64,
    pub blob_gasprice: u128,
}
*)
Module BlobExcessGasAndPrice.
  RocqOfRustLinkRecord "revm_context_interface::block::BlobExcessGasAndPrice" := {
    excess_blob_gas : u64;
    blob_gasprice : u128
  }.
End BlobExcessGasAndPrice.
Export (hints) BlobExcessGasAndPrice.
