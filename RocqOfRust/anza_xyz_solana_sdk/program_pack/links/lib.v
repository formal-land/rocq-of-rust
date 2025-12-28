Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
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
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("solana_program_pack::Pack", [], [], Φ Self).

  Definition Run_unpack (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "unpack" (fun method =>
      forall (input : Ref.t Pointer.Kind.Ref (list U8.t)),
        Run.Trait method [] [] [φ input] (Result.t Self ProgramError.t)
    ).

  Definition Run_unpack_unchecked (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "unpack_unchecked" (fun method =>
      forall (input : Ref.t Pointer.Kind.Ref (list U8.t)),
        Run.Trait method [] [] [φ input] (Result.t Self ProgramError.t)
    ).

  Definition Run_unpack_from_slice (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "unpack_from_slice" (fun method =>
      forall (src : Ref.t Pointer.Kind.Ref (list U8.t)),
        Run.Trait method [] [] [φ src] (Result.t Self ProgramError.t)
    ).

  Definition Run_pack (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "pack" (fun method =>
      forall (src : Self) (dst : Ref.t Pointer.Kind.MutRef (list U8.t)),
        Run.Trait method [] [] [φ src; φ dst] (Result.t unit ProgramError.t)
    ).

  Definition Run_pack_into_slice (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "pack_into_slice" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self) (dst : Ref.t Pointer.Kind.MutRef (list U8.t)),
        Run.Trait method [] [] [φ self; φ dst] unit
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    unpack : Run_unpack Self;
    unpack_unchecked : Run_unpack_unchecked Self;
    unpack_from_slice : Run_unpack_from_slice Self;
    pack : Run_pack Self;
    pack_into_slice : Run_pack_into_slice Self;
  }.
End Pack.
