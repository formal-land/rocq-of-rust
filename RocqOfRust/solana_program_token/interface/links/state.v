Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
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
  Inductive t : Set :=
  | Uninitialized
  | Initialized
  | Frozen.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "spl_token_interface::state::AccountState";
    φ x :=
      match x with
      | Uninitialized =>
          Value.StructTuple "spl_token_interface::state::AccountState::Uninitialized" [] [] []
      | Initialized =>
          Value.StructTuple "spl_token_interface::state::AccountState::Initialized" [] [] []
      | Frozen =>
          Value.StructTuple "spl_token_interface::state::AccountState::Frozen" [] [] []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "spl_token_interface::state::AccountState").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with_Uninitialized :
    Value.StructTuple "spl_token_interface::state::AccountState::Uninitialized" [] [] [] =
    φ Uninitialized.
  Proof. reflexivity. Qed.
  Definition of_value_Uninitialized :
    OfValue.t (Value.StructTuple "spl_token_interface::state::AccountState::Uninitialized" [] [] []).
  Proof. econstructor; apply of_value_with_Uninitialized. Defined.
  Smpl Add apply of_value_Uninitialized : of_value.

  Lemma of_value_with_Initialized :
    Value.StructTuple "spl_token_interface::state::AccountState::Initialized" [] [] [] =
    φ Initialized.
  Proof. reflexivity. Qed.
  Definition of_value_Initialized :
    OfValue.t (Value.StructTuple "spl_token_interface::state::AccountState::Initialized" [] [] []).
  Proof. econstructor; apply of_value_with_Initialized. Defined.
  Smpl Add apply of_value_Initialized : of_value.

  Lemma of_value_with_Frozen :
    Value.StructTuple "spl_token_interface::state::AccountState::Frozen" [] [] [] =
    φ Frozen.
  Proof. reflexivity. Qed.
  Definition of_value_Frozen :
    OfValue.t (Value.StructTuple "spl_token_interface::state::AccountState::Frozen" [] [] []).
  Proof. econstructor; apply of_value_with_Frozen. Defined.
  Smpl Add apply of_value_Frozen : of_value.
End AccountState.

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
  Record t : Set := {
    mint_authority : COption.t Address.t;
    supply : U64.t;
    decimals : U8.t;
    is_initialized : bool;
    freeze_authority : COption.t Address.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "spl_token_interface::state::Mint";
    φ x :=
      Value.StructRecord "spl_token_interface::state::Mint" [] [] [
        ("mint_authority", φ x.(mint_authority));
        ("supply", φ x.(supply));
        ("decimals", φ x.(decimals));
        ("is_initialized", φ x.(is_initialized));
        ("freeze_authority", φ x.(freeze_authority))
      ];
  }.

  Definition of_ty : OfTy.t (Ty.path "spl_token_interface::state::Mint").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with
    (mint_authority : COption.t Address.t) (mint_authority' : Value.t)
    (supply : U64.t) (supply' : Value.t)
    (decimals : U8.t) (decimals' : Value.t)
    (is_initialized : bool) (is_initialized' : Value.t)
    (freeze_authority : COption.t Address.t) (freeze_authority' : Value.t)
    :
    mint_authority' = φ mint_authority ->
    supply' = φ supply ->
    decimals' = φ decimals ->
    is_initialized' = φ is_initialized ->
    freeze_authority' = φ freeze_authority ->
    Value.StructRecord "spl_token_interface::state::Mint" [] [] [
      ("mint_authority", mint_authority');
      ("supply", supply');
      ("decimals", decimals');
      ("is_initialized", is_initialized');
      ("freeze_authority", freeze_authority')
    ] = φ (Build_t mint_authority supply decimals is_initialized freeze_authority).
  Proof. intros; subst; reflexivity. Qed.
  Smpl Add apply of_value_with : of_value.

  Module SubPointer.
    Definition get_mint_authority : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "spl_token_interface::state::Mint" "mint_authority") :=
    {|
      SubPointer.Runner.projection x := Some x.(mint_authority);
      SubPointer.Runner.injection x y := Some (x <| mint_authority := y |>);
    |}.

    Lemma get_mint_authority_is_valid :
      SubPointer.Runner.Valid.t get_mint_authority.
    Proof. now constructor. Qed.
    Smpl Add apply get_mint_authority_is_valid : run_sub_pointer.

    Definition get_supply : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "spl_token_interface::state::Mint" "supply") :=
    {|
      SubPointer.Runner.projection x := Some x.(supply);
      SubPointer.Runner.injection x y := Some (x <| supply := y |>);
    |}.

    Lemma get_supply_is_valid :
      SubPointer.Runner.Valid.t get_supply.
    Proof. now constructor. Qed.
    Smpl Add apply get_supply_is_valid : run_sub_pointer.

    Definition get_decimals : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "spl_token_interface::state::Mint" "decimals") :=
    {|
      SubPointer.Runner.projection x := Some x.(decimals);
      SubPointer.Runner.injection x y := Some (x <| decimals := y |>);
    |}.

    Lemma get_decimals_is_valid :
      SubPointer.Runner.Valid.t get_decimals.
    Proof. now constructor. Qed.
    Smpl Add apply get_decimals_is_valid : run_sub_pointer.

    Definition get_is_initialized : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "spl_token_interface::state::Mint" "is_initialized") :=
    {|
      SubPointer.Runner.projection x := Some x.(is_initialized);
      SubPointer.Runner.injection x y := Some (x <| is_initialized := y |>);
    |}.

    Lemma get_is_initialized_is_valid :
      SubPointer.Runner.Valid.t get_is_initialized.
    Proof. now constructor. Qed.
    Smpl Add apply get_is_initialized_is_valid : run_sub_pointer.

    Definition get_freeze_authority : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "spl_token_interface::state::Mint" "freeze_authority") :=
    {|
      SubPointer.Runner.projection x := Some x.(freeze_authority);
      SubPointer.Runner.injection x y := Some (x <| freeze_authority := y |>);
    |}.

    Lemma get_freeze_authority_is_valid :
      SubPointer.Runner.Valid.t get_freeze_authority.
    Proof. now constructor. Qed.
    Smpl Add apply get_freeze_authority_is_valid : run_sub_pointer.
  End SubPointer.
End Mint.

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
  Record t : Set := {
    mint : Address.t;
    owner : Address.t;
    amount : U64.t;
    delegate : COption.t Address.t;
    state : AccountState.t;
    is_native : COption.t U64.t;
    delegated_amount : U64.t;
    close_authority : COption.t Address.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "spl_token_interface::state::Account";
    φ x :=
      Value.StructRecord "spl_token_interface::state::Account" [] [] [
        ("mint", φ x.(mint));
        ("owner", φ x.(owner));
        ("amount", φ x.(amount));
        ("delegate", φ x.(delegate));
        ("state", φ x.(state));
        ("is_native", φ x.(is_native));
        ("delegated_amount", φ x.(delegated_amount));
        ("close_authority", φ x.(close_authority))
      ];
  }.

  Definition of_ty : OfTy.t (Ty.path "spl_token_interface::state::Account").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with
    (mint : Address.t) (mint' : Value.t)
    (owner : Address.t) (owner' : Value.t)
    (amount : U64.t) (amount' : Value.t)
    (delegate : COption.t Address.t) (delegate' : Value.t)
    (state : AccountState.t) (state' : Value.t)
    (is_native : COption.t U64.t) (is_native' : Value.t)
    (delegated_amount : U64.t) (delegated_amount' : Value.t)
    (close_authority : COption.t Address.t) (close_authority' : Value.t)
    :
    mint' = φ mint ->
    owner' = φ owner ->
    amount' = φ amount ->
    delegate' = φ delegate ->
    state' = φ state ->
    is_native' = φ is_native ->
    delegated_amount' = φ delegated_amount ->
    close_authority' = φ close_authority ->
    Value.StructRecord "spl_token_interface::state::Account" [] [] [
      ("mint", mint');
      ("owner", owner');
      ("amount", amount');
      ("delegate", delegate');
      ("state", state');
      ("is_native", is_native');
      ("delegated_amount", delegated_amount');
      ("close_authority", close_authority')
    ] = φ (Build_t mint owner amount delegate state is_native delegated_amount close_authority).
  Proof. intros; subst; reflexivity. Qed.
  Smpl Add apply of_value_with : of_value.

  Module SubPointer.
    Definition get_mint : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "spl_token_interface::state::Account" "mint") :=
    {|
      SubPointer.Runner.projection x := Some x.(mint);
      SubPointer.Runner.injection x y := Some (x <| mint := y |>);
    |}.

    Lemma get_mint_is_valid :
      SubPointer.Runner.Valid.t get_mint.
    Proof. now constructor. Qed.
    Smpl Add apply get_mint_is_valid : run_sub_pointer.

    Definition get_owner : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "spl_token_interface::state::Account" "owner") :=
    {|
      SubPointer.Runner.projection x := Some x.(owner);
      SubPointer.Runner.injection x y := Some (x <| owner := y |>);
    |}.

    Lemma get_owner_is_valid :
      SubPointer.Runner.Valid.t get_owner.
    Proof. now constructor. Qed.
    Smpl Add apply get_owner_is_valid : run_sub_pointer.

    Definition get_amount : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "spl_token_interface::state::Account" "amount") :=
    {|
      SubPointer.Runner.projection x := Some x.(amount);
      SubPointer.Runner.injection x y := Some (x <| amount := y |>);
    |}.

    Lemma get_amount_is_valid :
      SubPointer.Runner.Valid.t get_amount.
    Proof. now constructor. Qed.
    Smpl Add apply get_amount_is_valid : run_sub_pointer.

    Definition get_delegate : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "spl_token_interface::state::Account" "delegate") :=
    {|
      SubPointer.Runner.projection x := Some x.(delegate);
      SubPointer.Runner.injection x y := Some (x <| delegate := y |>);
    |}.

    Lemma get_delegate_is_valid :
      SubPointer.Runner.Valid.t get_delegate.
    Proof. now constructor. Qed.
    Smpl Add apply get_delegate_is_valid : run_sub_pointer.

    Definition get_state : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "spl_token_interface::state::Account" "state") :=
    {|
      SubPointer.Runner.projection x := Some x.(state);
      SubPointer.Runner.injection x y := Some (x <| state := y |>);
    |}.

    Lemma get_state_is_valid :
      SubPointer.Runner.Valid.t get_state.
    Proof. now constructor. Qed.
    Smpl Add apply get_state_is_valid : run_sub_pointer.

    Definition get_is_native : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "spl_token_interface::state::Account" "is_native") :=
    {|
      SubPointer.Runner.projection x := Some x.(is_native);
      SubPointer.Runner.injection x y := Some (x <| is_native := y |>);
    |}.

    Lemma get_is_native_is_valid :
      SubPointer.Runner.Valid.t get_is_native.
    Proof. now constructor. Qed.
    Smpl Add apply get_is_native_is_valid : run_sub_pointer.

    Definition get_delegated_amount : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "spl_token_interface::state::Account" "delegated_amount") :=
    {|
      SubPointer.Runner.projection x := Some x.(delegated_amount);
      SubPointer.Runner.injection x y := Some (x <| delegated_amount := y |>);
    |}.

    Lemma get_delegated_amount_is_valid :
      SubPointer.Runner.Valid.t get_delegated_amount.
    Proof. now constructor. Qed.
    Smpl Add apply get_delegated_amount_is_valid : run_sub_pointer.

    Definition get_close_authority : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "spl_token_interface::state::Account" "close_authority") :=
    {|
      SubPointer.Runner.projection x := Some x.(close_authority);
      SubPointer.Runner.injection x y := Some (x <| close_authority := y |>);
    |}.

    Lemma get_close_authority_is_valid :
      SubPointer.Runner.Valid.t get_close_authority.
    Proof. now constructor. Qed.
    Smpl Add apply get_close_authority_is_valid : run_sub_pointer.
  End SubPointer.
End Account.

(* impl Account *)
Module Impl_Account.
  Definition Self : Set := Account.t.

  (* pub fn is_frozen(&self) -> bool *)
  Instance run_is_frozen
      (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait state.Impl_spl_token_interface_state_Account.is_frozen [] [] [φ self]
      bool.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_is_frozen.

  (* pub fn is_native(&self) -> bool *)
  Instance run_is_native
      (self : Ref.t Pointer.Kind.Ref Self) :
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
Export Impl_Pack_for_Mint.

(* impl Pack for Account *)
Module Impl_Pack_for_Account.
  Instance run : Pack.Run Account.t.
  Admitted.
End Impl_Pack_for_Account.
Export Impl_Pack_for_Account.
