Require Import links.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.links.aliases.
Require Import core.links.option.
Require Import revm.revm_context_interface.block.links.blob.
Require Import ruint.links.lib.

(*
#[auto_impl(&, &mut, Box, Arc)]
pub trait Block {
    fn number(&self) -> u64;
    fn beneficiary(&self) -> Address;
    fn timestamp(&self) -> u64;
    fn gas_limit(&self) -> u64;
    fn basefee(&self) -> u64;
    fn difficulty(&self) -> U256;
    fn prevrandao(&self) -> Option<B256>;
    fn blob_excess_gas_and_price(&self) -> Option<BlobExcessGasAndPrice>;
    fn blob_gasprice(&self) -> Option<u128> {
        self.blob_excess_gas_and_price().map(|a| a.blob_gasprice)
    }
    fn blob_excess_gas(&self) -> Option<u64> {
        self.blob_excess_gas_and_price().map(|a| a.excess_blob_gas)
    }
}
*)
Module Block. 
  Parameter t : Set.

  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_context_interface::block::Block";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_number (Self : Set) `{Link Self} : Set := {
    number : PolymorphicFunction.t;
    number_is_method :: IsTraitMethod.C (trait Self) "number" number;
    run_number (self : '& Self) :: Run.Trait number [] [] [ φ self ] u64;
  }.

  Class Method_beneficiary (Self : Set) `{Link Self} : Set := {
    beneficiary : PolymorphicFunction.t;
    beneficiary_is_method :: IsTraitMethod.C (trait Self) "beneficiary" beneficiary;
    run_beneficiary (self : '& Self) :: Run.Trait beneficiary [] [] [ φ self ] Address.t;
  }.

  Class Method_timestamp (Self : Set) `{Link Self} : Set := {
    timestamp : PolymorphicFunction.t;
    timestamp_is_method :: IsTraitMethod.C (trait Self) "timestamp" timestamp;
    run_timestamp (self : '& Self) :: Run.Trait timestamp [] [] [ φ self ] u64;
  }.

  Class Method_gas_limit (Self : Set) `{Link Self} : Set := {
    gas_limit : PolymorphicFunction.t;
    gas_limit_is_method :: IsTraitMethod.C (trait Self) "gas_limit" gas_limit;
    run_gas_limit (self : '& Self) :: Run.Trait gas_limit [] [] [ φ self ] u64;
  }.

  Class Method_basefee (Self : Set) `{Link Self} : Set := {
    basefee : PolymorphicFunction.t;
    basefee_is_method :: IsTraitMethod.C (trait Self) "basefee" basefee;
    run_basefee (self : '& Self) :: Run.Trait basefee [] [] [ φ self ] u64;
  }.

  Class Method_difficulty (Self : Set) `{Link Self} : Set := {
    difficulty : PolymorphicFunction.t;
    difficulty_is_method :: IsTraitMethod.C (trait Self) "difficulty" difficulty;
    run_difficulty (self : '& Self) :: Run.Trait difficulty [] [] [ φ self ] aliases.U256.t;
  }.

  Class Method_prevrandao (Self : Set) `{Link Self} : Set := {
    prevrandao : PolymorphicFunction.t;
    prevrandao_is_method :: IsTraitMethod.C (trait Self) "prevrandao" prevrandao;
    run_prevrandao (self : '& Self) :: Run.Trait prevrandao [] [] [ φ self ] (option aliases.B256.t);
  }.

  Class Method_blob_excess_gas_and_price (Self : Set) `{Link Self} : Set := {
    blob_excess_gas_and_price : PolymorphicFunction.t;
    blob_excess_gas_and_price_is_method :: IsTraitMethod.C (trait Self) "blob_excess_gas_and_price" blob_excess_gas_and_price;
    run_blob_excess_gas_and_price (self : '& Self) :: Run.Trait blob_excess_gas_and_price [] [] [ φ self ] (option BlobExcessGasAndPrice.t);
  }.

  Class Method_blob_gasprice (Self : Set) `{Link Self} : Set := {
    blob_gasprice : PolymorphicFunction.t;
    blob_gasprice_is_method :: IsTraitMethod.C (trait Self) "blob_gasprice" blob_gasprice;
    run_blob_gasprice (self : '& Self) :: Run.Trait blob_gasprice [] [] [ φ self ] (option u128);
  }.

  Class Method_blob_excess_gas (Self : Set) `{Link Self} : Set := {
    blob_excess_gas : PolymorphicFunction.t;
    blob_excess_gas_is_method :: IsTraitMethod.C (trait Self) "blob_excess_gas" blob_excess_gas;
    run_blob_excess_gas (self : '& Self) :: Run.Trait blob_excess_gas [] [] [ φ self ] (option u64);
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    method_number :: Method_number Self;
    method_beneficiary :: Method_beneficiary Self;
    method_timestamp :: Method_timestamp Self;
    method_gas_limit :: Method_gas_limit Self;
    method_basefee :: Method_basefee Self;
    method_difficulty :: Method_difficulty Self;
    method_prevrandao :: Method_prevrandao Self;
    method_blob_excess_gas_and_price :: Method_blob_excess_gas_and_price Self;
    method_blob_gasprice :: Method_blob_gasprice Self;
    method_blob_excess_gas :: Method_blob_excess_gas Self;
  }.
End Block.
Export (hints) Block. 

(*
#[auto_impl(&, &mut, Box, Arc)]
pub trait BlockGetter {
    type Block: Block;

    fn block(&self) -> &Self::Block;
}
*)
Module BlockGetter.
  Module Types.
    Record t : Type := {
      Block : Set;
    }.

    Class AreLinks (types : t) : Set := {
      H_Block : Link types.(Block);
    }.

    Global Instance IsLinkBlock (types : t) (H : AreLinks types) : Link types.(Block) :=
      H.(H_Block _).
  End Types.

  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_context_interface::block::BlockGetter";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_block (Self : Set) `{Link Self} (types : Types.t) `{Types.AreLinks types} : Set := {
    block : PolymorphicFunction.t;
    block_is_method :: IsTraitMethod.C (trait Self) "block" block;
    run_block (self : '& Self) :: Run.Trait block [] [] [ φ self ] ('& types.(Types.Block));
  }.

  Class Run (Self : Set) `{Link Self} (types : Types.t) `{Types.AreLinks types} : Set := {
    Block_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::block::BlockGetter" [] [] (Φ Self)
        "Block" (Φ types.(Types.Block));
    run_Block_for_Block :: Block.Run types.(Types.Block);
    method_block :: Method_block Self types;
  }.
End BlockGetter.
Export (hints) BlockGetter.