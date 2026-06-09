Require Import links.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.links.aliases.
Require Import core.array.links.mod.
Require Import core.convert.links.mod.
Require Import core.fmt.links.mod.
Require Import core.iter.traits.links.collect.
Require Import core.links.panicking.
Require Import core.num.links.mod.
Require Import core.ptr.links.mut_ptr.
Require Import core.slice.links.iter.
Require Import core.slice.links.mod.
Require Import revm.revm_interpreter.instructions.utility.
Require Import ruint.links.bytes.
Require Import ruint.links.lib.

Module IntoU256.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_interpreter::instructions::utility::IntoU256";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_into_u256 (Self : Set) `{Link Self} : Set := {
    into_u256 : PolymorphicFunction.t;
    into_u256_is_method :: IsTraitMethod.C (trait Self) "into_u256" into_u256;
    run_into_u256 (self : Self) :: Run.Trait into_u256 [] [] [ φ self ] aliases.U256.t;
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    method_into_u256 :: Method_into_u256 Self;
  }.
End IntoU256.
Export (hints) IntoU256.

(* impl IntoU256 for B256 { *)
Module Impl_IntoU256_for_B256.
  Definition Self : Set :=
    aliases.B256.t.

  Instance run_into_u256 (self : Self) :
    Run.Trait
      instructions.utility.Impl_revm_interpreter_instructions_utility_IntoU256_for_alloy_primitives_bits_fixed_FixedBytes_Usize_32.into_u256
      [] [] [φ self] aliases.U256.t.
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_into_u256.

  (* fn into_u256(self) -> U256 *)
  Instance method_into_u256 : IntoU256.Method_into_u256 Self.
  Proof.
    econstructor.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply instructions.utility.Impl_revm_interpreter_instructions_utility_IntoU256_for_alloy_primitives_bits_fixed_FixedBytes_Usize_32.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run : IntoU256.Run Self := {}.
End Impl_IntoU256_for_B256.
Export (hints) Impl_IntoU256_for_B256.

(* impl IntoU256 for Address { *)
Module Impl_IntoU256_for_Address.
  Definition Self : Set :=
    Address.t.

  Instance run_into_u256 (self : Self) :
    Run.Trait
      instructions.utility.Impl_revm_interpreter_instructions_utility_IntoU256_for_alloy_primitives_bits_address_Address.into_u256
      [] [] [φ self] aliases.U256.t.
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_into_u256.

  (* fn into_u256(self) -> U256 *)
  Instance method_into_u256 : IntoU256.Method_into_u256 Self.
  Proof.
    econstructor.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply instructions.utility.Impl_revm_interpreter_instructions_utility_IntoU256_for_alloy_primitives_bits_address_Address.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run : IntoU256.Run Self := {}.
End Impl_IntoU256_for_Address.
Export (hints) Impl_IntoU256_for_Address.

(*
pub trait IntoAddress {
    fn into_address(self) -> Address;
}
*)
Module IntoAddress.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_interpreter::instructions::utility::IntoAddress";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_into_address (Self : Set) `{Link Self} : Set := {
    into_address : PolymorphicFunction.t;
    into_address_is_method :: IsTraitMethod.C (trait Self) "into_address" into_address;
    run_into_address (self : Self) :: Run.Trait into_address [] [] [ φ self ] Address.t;
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    method_into_address :: Method_into_address Self;
  }.
End IntoAddress.
Export (hints) IntoAddress.

(* impl IntoAddress for U256 { *)
Module Impl_IntoAddress_for_U256.
  Definition Self : Set :=
    aliases.U256.t.

  Instance run_into_address (self : Self) :
    Run.Trait
      instructions.utility.Impl_revm_interpreter_instructions_utility_IntoAddress_for_ruint_Uint_Usize_256_Usize_4.into_address
      [] [] [φ self] Address.t.
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_into_address.

  (* fn into_address(self) -> Address *)
  Instance method_into_address : IntoAddress.Method_into_address Self.
  Proof.
    econstructor.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply instructions.utility.Impl_revm_interpreter_instructions_utility_IntoAddress_for_ruint_Uint_Usize_256_Usize_4.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run : IntoAddress.Run Self := {}.
End Impl_IntoAddress_for_U256.
Export (hints) Impl_IntoAddress_for_U256.
