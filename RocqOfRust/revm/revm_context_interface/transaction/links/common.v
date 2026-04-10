Require Import links.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import ruint.links.lib.

(*
pub trait CommonTxFields {
    fn caller(&self) -> Address;
    fn gas_limit(&self) -> u64;
    fn value(&self) -> U256;
    fn input(&self) -> &Bytes;
    fn nonce(&self) -> u64;
}
*)
Module CommonTxFields.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_context_interface::transaction::common::CommonTxFields";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_caller (Self : Set) `{Link Self} : Set := {
    caller : PolymorphicFunction.t;
    caller_is_method :: IsTraitMethod.C (trait Self) "caller" caller;
    run_caller (self : '& Self) :: Run.Trait caller [] [] [ φ self ] Address.t;
  }.

  Class Method_gas_limit (Self : Set) `{Link Self} : Set := {
    gas_limit : PolymorphicFunction.t;
    gas_limit_is_method :: IsTraitMethod.C (trait Self) "gas_limit" gas_limit;
    run_gas_limit (self : '& Self) :: Run.Trait gas_limit [] [] [ φ self ] u64;
  }.

  Class Method_value (Self : Set) `{Link Self} : Set := {
    value : PolymorphicFunction.t;
    value_is_method :: IsTraitMethod.C (trait Self) "value" value;
    run_value (self : '& Self) :: Run.Trait value [] [] [ φ self ] aliases.U256.t;
  }.

  Class Method_input (Self : Set) `{Link Self} : Set := {
    input : PolymorphicFunction.t;
    input_is_method :: IsTraitMethod.C (trait Self) "input" input;
    run_input (self : '& Self) :: Run.Trait input [] [] [ φ self ] ('& Bytes.t);
  }.

  Class Method_nonce (Self : Set) `{Link Self} : Set := {
    nonce : PolymorphicFunction.t;
    nonce_is_method :: IsTraitMethod.C (trait Self) "nonce" nonce;
    run_nonce (self : '& Self) :: Run.Trait nonce [] [] [ φ self ] u64;
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    method_caller :: Method_caller Self;
    method_gas_limit :: Method_gas_limit Self;
    method_value :: Method_value Self;
    method_input :: Method_input Self;
    method_nonce :: Method_nonce Self;
  }.
End CommonTxFields.
Export (hints) CommonTxFields.
