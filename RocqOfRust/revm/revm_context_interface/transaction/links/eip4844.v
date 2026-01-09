Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.links.aliases.
Require Import ruint.links.lib.

(*
pub trait Eip4844Tx: Eip1559CommonTxFields {
    fn destination(&self) -> Address;
    fn blob_versioned_hashes(&self) -> &[B256];
    fn max_fee_per_blob_gas(&self) -> u128;
    fn total_blob_gas(&self) -> u64;
    fn calc_max_data_fee(&self) -> U256;
}
*)
Module Eip4844Tx.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_context_interface::transaction::eip4844::Eip4844Tx";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_destination (Self : Set) `{Link Self} : Set := {
    destination : PolymorphicFunction.t;
    destination_is_method :: IsTraitMethod.C (trait Self) "destination" destination;
    run_destination (self : '& Self) :: Run.Trait destination [] [] [ φ self ] Address.t;
  }.

  Class Method_blob_versioned_hashes (Self : Set) `{Link Self} : Set := {
    blob_versioned_hashes : PolymorphicFunction.t;
    blob_versioned_hashes_is_method :: IsTraitMethod.C (trait Self) "blob_versioned_hashes" blob_versioned_hashes;
    run_blob_versioned_hashes (self : '& Self) :: Run.Trait blob_versioned_hashes [] [] [ φ self ] ('& (list aliases.B256.t));
  }.

  Class Method_max_fee_per_blob_gas (Self : Set) `{Link Self} : Set := {
    max_fee_per_blob_gas : PolymorphicFunction.t;
    max_fee_per_blob_gas_is_method :: IsTraitMethod.C (trait Self) "max_fee_per_blob_gas" max_fee_per_blob_gas;
    run_max_fee_per_blob_gas (self : '& Self) :: Run.Trait max_fee_per_blob_gas [] [] [ φ self ] u128;
  }.

  Class Method_total_blob_gas (Self : Set) `{Link Self} : Set := {
    total_blob_gas : PolymorphicFunction.t;
    total_blob_gas_is_method :: IsTraitMethod.C (trait Self) "total_blob_gas" total_blob_gas;
    run_total_blob_gas (self : '& Self) :: Run.Trait total_blob_gas [] [] [ φ self ] u64;
  }.

  Class Method_calc_max_data_fee (Self : Set) `{Link Self} : Set := {
    calc_max_data_fee : PolymorphicFunction.t;
    calc_max_data_fee_is_method :: IsTraitMethod.C (trait Self) "calc_max_data_fee" calc_max_data_fee;
    run_calc_max_data_fee (self : '& Self) :: Run.Trait calc_max_data_fee [] [] [ φ self ] aliases.U256.t;
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    (* TODO *)
    (* run_Eip1559CommonTxFields_for_Self : Eip1559CommonTxFields.Run Self; *)
    method_destination :: Method_destination Self;
    method_blob_versioned_hashes :: Method_blob_versioned_hashes Self;
    method_max_fee_per_blob_gas :: Method_max_fee_per_blob_gas Self;
    method_total_blob_gas :: Method_total_blob_gas Self;
    method_calc_max_data_fee :: Method_calc_max_data_fee Self;
  }.
End Eip4844Tx.
Export (hints) Eip4844Tx.
