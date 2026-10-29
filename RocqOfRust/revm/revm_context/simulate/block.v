Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_context_interface.block.links.blob.
Require Import ruint.links.lib.

Module BlockEnv.
  Record t : Set := {
    number : aliases.U256.t;
    beneficiary : Address.t;
    timestamp : aliases.U256.t;
    gas_limit : u64;
    basefee : u64;
    difficulty : aliases.U256.t;
    prevrandao : option aliases.B256.t;
    blob_excess_gas_and_price : option BlobExcessGasAndPrice.t;
  }.
End BlockEnv.

Module Impl_Default_for_BlockEnv.
  Definition default : BlockEnv.t := {|
    BlockEnv.number := {| Uint.value := 0 |};
    BlockEnv.beneficiary := {| Address.value := 0 |};
    BlockEnv.timestamp := {| Uint.value := 1 |};
    BlockEnv.gas_limit := {| Integer.value := 2 ^ 64 - 1 |};
    BlockEnv.basefee := 0;
    BlockEnv.difficulty := {| Uint.value := 0 |};
    BlockEnv.prevrandao := Some (FixedBytes.from_Z 0);
    BlockEnv.blob_excess_gas_and_price := Some {|
      BlobExcessGasAndPrice.excess_blob_gas := 0;
      BlobExcessGasAndPrice.blob_gasprice := 1 |};
  |}.
End Impl_Default_for_BlockEnv.

Module Impl_Block_for_BlockEnv.
  Definition blob_gasprice (self : BlockEnv.t) : option u128 :=
    option_map BlobExcessGasAndPrice.blob_gasprice self.(BlockEnv.blob_excess_gas_and_price).

  Definition blob_excess_gas (self : BlockEnv.t) : option u64 :=
    option_map BlobExcessGasAndPrice.excess_blob_gas self.(BlockEnv.blob_excess_gas_and_price).
End Impl_Block_for_BlockEnv.
