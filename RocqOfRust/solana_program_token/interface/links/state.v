Require Import links.RocqOfRust.
Require Import anza_xyz_solana_sdk.address.links.lib.
Require Import anza_xyz_solana_sdk.program_error.links.lib.
Require Import anza_xyz_solana_sdk.program_option.links.lib.
Require Import anza_xyz_solana_sdk.program_pack.links.lib.
Require Import solana_program_token.interface.state.

(*
  pub enum AccountState {
      Uninitialized,
      Initialized,
      Frozen,
  }
*)
Module AccountState.
  RocqOfRustLinkEnum "spl_token_interface::state::AccountState" :=
  | Uninitialized
  | Initialized
  | Frozen
  .
End AccountState.
Export (hints) AccountState.

(*
  pub struct Mint {
      pub mint_authority: COption<Pubkey>,
      pub supply: u64,
      pub decimals: u8,
      pub is_initialized: bool,
      pub freeze_authority: COption<Pubkey>,
  }
*)
Module Mint.
  RocqOfRustLinkRecord "spl_token_interface::state::Mint" := {
    mint_authority : (COption.t Address.t);
    supply : u64;
    decimals : u8;
    is_initialized : bool;
    freeze_authority : (COption.t Address.t)
  }.
End Mint.
Export (hints) Mint.

(*
  pub struct Account {
      pub mint: Pubkey,
      pub owner: Pubkey,
      pub amount: u64,
      pub delegate: COption<Pubkey>,
      pub state: AccountState,
      pub is_native: COption<u64>,
      pub delegated_amount: u64,
      pub close_authority: COption<Pubkey>,
  }
*)
Module Account.
  RocqOfRustLinkRecord "spl_token_interface::state::Account" := {
    mint : Address.t;
    owner : Address.t;
    amount : u64;
    delegate : (COption.t Address.t);
    state : AccountState.t;
    is_native : (COption.t u64);
    delegated_amount : u64;
    close_authority : (COption.t Address.t)
  }.
End Account.
Export (hints) Account.

(* impl Account *)
Module Impl_Account.
  Definition Self : Set := Account.t.

  (* pub fn is_frozen(&self) -> bool *)
  Instance run_is_frozen
      (self : '& Self) :
    Run.Trait state.Impl_spl_token_interface_state_Account.is_frozen [] [] [φ self]
      bool.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_is_frozen.

  (* pub fn is_native(&self) -> bool *)
  Instance run_is_native
      (self : '& Self) :
    Run.Trait state.Impl_spl_token_interface_state_Account.is_native [] [] [φ self]
      bool.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_is_native.
End Impl_Account.
Export (hints) Impl_Account.

(* impl Pack for Mint *)
Module Impl_Pack_for_Mint.
  Instance run : Pack.Run Mint.t.
  Admitted.
End Impl_Pack_for_Mint.
Export (hints) Impl_Pack_for_Mint.

(* impl Pack for Account *)
Module Impl_Pack_for_Account.
  Instance run : Pack.Run Account.t.
  Admitted.
End Impl_Pack_for_Account.
Export (hints) Impl_Pack_for_Account.
