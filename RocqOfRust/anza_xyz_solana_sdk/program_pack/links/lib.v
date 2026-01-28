Require Import links.RocqOfRust.
Require Import anza_xyz_solana_sdk.program_error.links.lib.
Require Import anza_xyz_solana_sdk.program_pack.lib.
Require Import core.links.result.

(*
  pub trait Pack: Sealed + Sized {
      const LEN: usize;
      fn unpack_from_slice(src: &[u8]) -> Result<Self, ProgramError>;
      fn pack_into_slice(&self, dst: &mut [u8]);

      // Provided methods
      fn get_packed_len() -> usize { ... }
      fn unpack(input: &[u8]) -> Result<Self, ProgramError> { ... }
      fn unpack_unchecked(input: &[u8]) -> Result<Self, ProgramError> { ... }
      fn pack(src: Self, dst: &mut [u8]) -> Result<(), ProgramError> { ... }
  }
*)
Module Pack.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "solana_program_pack::Pack";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_unpack (Self : Set) `{Link Self} : Set := {
    unpack : PolymorphicFunction.t;
    unpack_is_method :: IsTraitMethod.C (trait Self) "unpack" unpack;
    run_unpack (input : '& (list u8)) :: Run.Trait unpack [] [] [φ input] (Result.t Self ProgramError.t);
  }.

  Class Method_unpack_unchecked (Self : Set) `{Link Self} : Set := {
    unpack_unchecked : PolymorphicFunction.t;
    unpack_unchecked_is_method :: IsTraitMethod.C (trait Self) "unpack_unchecked" unpack_unchecked;
    run_unpack_unchecked (input : '& (list u8)) :: Run.Trait unpack_unchecked [] [] [φ input] (Result.t Self ProgramError.t);
  }.

  Class Method_unpack_from_slice (Self : Set) `{Link Self} : Set := {
    unpack_from_slice : PolymorphicFunction.t;
    unpack_from_slice_is_method :: IsTraitMethod.C (trait Self) "unpack_from_slice" unpack_from_slice;
    run_unpack_from_slice (src : '& (list u8)) :: Run.Trait unpack_from_slice [] [] [φ src] (Result.t Self ProgramError.t);
  }.

  Class Method_pack (Self : Set) `{Link Self} : Set := {
    pack : PolymorphicFunction.t;
    pack_is_method :: IsTraitMethod.C (trait Self) "pack" pack;
    run_pack (src : Self) (dst : '&mut (list u8)) :: Run.Trait pack [] [] [φ src; φ dst] (Result.t unit ProgramError.t);
  }.

  Class Method_pack_into_slice (Self : Set) `{Link Self} : Set := {
    pack_into_slice : PolymorphicFunction.t;
    pack_into_slice_is_method :: IsTraitMethod.C (trait Self) "pack_into_slice" pack_into_slice;
    run_pack_into_slice (self : '& Self) (dst : '&mut (list u8)) :: Run.Trait pack_into_slice [] [] [φ self; φ dst] unit;
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    method_unpack :: Method_unpack Self;
    method_unpack_unchecked :: Method_unpack_unchecked Self;
    method_unpack_from_slice :: Method_unpack_from_slice Self;
    method_pack :: Method_pack Self;
    method_pack_into_slice :: Method_pack_into_slice Self;
  }.
End Pack.
Export (hints) Pack.
