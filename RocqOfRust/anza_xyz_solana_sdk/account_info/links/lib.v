Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import anza_xyz_solana_sdk.address.links.lib.
Require Import anza_xyz_solana_sdk.program_error.links.lib.
Require Import core.links.result.
Require Import anza_xyz_solana_sdk.account_info.lib.

Instance run_MAX_PERMITTED_DATA_INCREASE :
  Run.Trait
    lib.value_MAX_PERMITTED_DATA_INCREASE [] [] []
    (Ref.t Pointer.Kind.Raw Usize.t).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_MAX_PERMITTED_DATA_INCREASE.

(*
  pub struct AccountInfo<'a> {
    pub key: &'a Pubkey,
    pub lamports: Rc<RefCell<&'a mut u64>>,
    pub data: Rc<RefCell<&'a mut [u8]>>,
    pub owner: &'a Pubkey,
    pub _unused: u64,
    pub is_signer: bool,
    pub is_writable: bool,
    pub executable: bool,
  }
*)
Module AccountInfo.
  (* Opaque representation of Rc<RefCell<&mut u64>> *)
  Parameter Rc_RefCell_mut_u64 : Set.
  Parameter Rc_RefCell_mut_u64_IsLink : Link Rc_RefCell_mut_u64.
  Global Existing Instance Rc_RefCell_mut_u64_IsLink.

  (* Opaque representation of Rc<RefCell<&mut [u8]>> *)
  Parameter Rc_RefCell_mut_slice_u8 : Set.
  Parameter Rc_RefCell_mut_slice_u8_IsLink : Link Rc_RefCell_mut_slice_u8.
  Global Existing Instance Rc_RefCell_mut_slice_u8_IsLink.

  Record t : Set := {
    key : Ref.t Pointer.Kind.Ref Address.t;
    lamports : Rc_RefCell_mut_u64;
    data : Rc_RefCell_mut_slice_u8;
    owner : Ref.t Pointer.Kind.Ref Address.t;
    _unused : U64.t;
    is_signer : bool;
    is_writable : bool;
    executable : bool;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "solana_account_info::AccountInfo";
    φ x :=
      Value.StructRecord "solana_account_info::AccountInfo" [] [] [
        ("key", φ x.(key));
        ("lamports", φ x.(lamports));
        ("data", φ x.(data));
        ("owner", φ x.(owner));
        ("_unused", φ x.(_unused));
        ("is_signer", φ x.(is_signer));
        ("is_writable", φ x.(is_writable));
        ("executable", φ x.(executable))
      ];
  }.

  Definition of_ty : OfTy.t (Ty.path "solana_account_info::AccountInfo").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with
    (key : Ref.t Pointer.Kind.Ref Address.t) (key' : Value.t)
    (lamports : Rc_RefCell_mut_u64) (lamports' : Value.t)
    (data : Rc_RefCell_mut_slice_u8) (data' : Value.t)
    (owner : Ref.t Pointer.Kind.Ref Address.t) (owner' : Value.t)
    (_unused : U64.t) (_unused' : Value.t)
    (is_signer : bool) (is_signer' : Value.t)
    (is_writable : bool) (is_writable' : Value.t)
    (executable : bool) (executable' : Value.t)
    :
    key' = φ key ->
    lamports' = φ lamports ->
    data' = φ data ->
    owner' = φ owner ->
    _unused' = φ _unused ->
    is_signer' = φ is_signer ->
    is_writable' = φ is_writable ->
    executable' = φ executable ->
    Value.StructRecord "solana_account_info::AccountInfo" [] [] [
      ("key", key');
      ("lamports", lamports');
      ("data", data');
      ("owner", owner');
      ("_unused", _unused');
      ("is_signer", is_signer');
      ("is_writable", is_writable');
      ("executable", executable')
    ] = φ (Build_t key lamports data owner _unused is_signer is_writable executable).
  Proof. intros; subst; reflexivity. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value
    (key : Ref.t Pointer.Kind.Ref Address.t) (key' : Value.t)
    (lamports : Rc_RefCell_mut_u64) (lamports' : Value.t)
    (data : Rc_RefCell_mut_slice_u8) (data' : Value.t)
    (owner : Ref.t Pointer.Kind.Ref Address.t) (owner' : Value.t)
    (_unused : U64.t) (_unused' : Value.t)
    (is_signer : bool) (is_signer' : Value.t)
    (is_writable : bool) (is_writable' : Value.t)
    (executable : bool) (executable' : Value.t)
    :
    key' = φ key ->
    lamports' = φ lamports ->
    data' = φ data ->
    owner' = φ owner ->
    _unused' = φ _unused ->
    is_signer' = φ is_signer ->
    is_writable' = φ is_writable ->
    executable' = φ executable ->
    OfValue.t (
      Value.StructRecord "solana_account_info::AccountInfo" [] [] [
        ("key", key');
        ("lamports", lamports');
        ("data", data');
        ("owner", owner');
        ("_unused", _unused');
        ("is_signer", is_signer');
        ("is_writable", is_writable');
        ("executable", executable')
      ]).
  Proof. econstructor; apply of_value_with; eassumption. Defined.
  Smpl Add apply of_value : of_value.

  Module SubPointer.
    Definition get_key : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "solana_account_info::AccountInfo" "key") :=
    {|
      SubPointer.Runner.projection x := Some x.(key);
      SubPointer.Runner.injection x y := Some (x <| key := y |>);
    |}.

    Lemma get_key_is_valid :
      SubPointer.Runner.Valid.t get_key.
    Proof. now constructor. Qed.
    Smpl Add apply get_key_is_valid : run_sub_pointer.

    Definition get_lamports : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "solana_account_info::AccountInfo" "lamports") :=
    {|
      SubPointer.Runner.projection x := Some x.(lamports);
      SubPointer.Runner.injection x y := Some (x <| lamports := y |>);
    |}.

    Lemma get_lamports_is_valid :
      SubPointer.Runner.Valid.t get_lamports.
    Proof. now constructor. Qed.
    Smpl Add apply get_lamports_is_valid : run_sub_pointer.

    Definition get_data : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "solana_account_info::AccountInfo" "data") :=
    {|
      SubPointer.Runner.projection x := Some x.(data);
      SubPointer.Runner.injection x y := Some (x <| data := y |>);
    |}.

    Lemma get_data_is_valid :
      SubPointer.Runner.Valid.t get_data.
    Proof. now constructor. Qed.
    Smpl Add apply get_data_is_valid : run_sub_pointer.

    Definition get_owner : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "solana_account_info::AccountInfo" "owner") :=
    {|
      SubPointer.Runner.projection x := Some x.(owner);
      SubPointer.Runner.injection x y := Some (x <| owner := y |>);
    |}.

    Lemma get_owner_is_valid :
      SubPointer.Runner.Valid.t get_owner.
    Proof. now constructor. Qed.
    Smpl Add apply get_owner_is_valid : run_sub_pointer.

    Definition get__unused : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "solana_account_info::AccountInfo" "_unused") :=
    {|
      SubPointer.Runner.projection x := Some x.(_unused);
      SubPointer.Runner.injection x y := Some (x <| _unused := y |>);
    |}.

    Lemma get__unused_is_valid :
      SubPointer.Runner.Valid.t get__unused.
    Proof. now constructor. Qed.
    Smpl Add apply get__unused_is_valid : run_sub_pointer.

    Definition get_is_signer : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "solana_account_info::AccountInfo" "is_signer") :=
    {|
      SubPointer.Runner.projection x := Some x.(is_signer);
      SubPointer.Runner.injection x y := Some (x <| is_signer := y |>);
    |}.

    Lemma get_is_signer_is_valid :
      SubPointer.Runner.Valid.t get_is_signer.
    Proof. now constructor. Qed.
    Smpl Add apply get_is_signer_is_valid : run_sub_pointer.

    Definition get_is_writable : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "solana_account_info::AccountInfo" "is_writable") :=
    {|
      SubPointer.Runner.projection x := Some x.(is_writable);
      SubPointer.Runner.injection x y := Some (x <| is_writable := y |>);
    |}.

    Lemma get_is_writable_is_valid :
      SubPointer.Runner.Valid.t get_is_writable.
    Proof. now constructor. Qed.
    Smpl Add apply get_is_writable_is_valid : run_sub_pointer.

    Definition get_executable : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "solana_account_info::AccountInfo" "executable") :=
    {|
      SubPointer.Runner.projection x := Some x.(executable);
      SubPointer.Runner.injection x y := Some (x <| executable := y |>);
    |}.

    Lemma get_executable_is_valid :
      SubPointer.Runner.Valid.t get_executable.
    Proof. now constructor. Qed.
    Smpl Add apply get_executable_is_valid : run_sub_pointer.
  End SubPointer.
End AccountInfo.

(*
  pub fn next_account_info<'a, 'b, I: Iterator<Item = &'a AccountInfo<'b>>>(
      iter: &mut I,
  ) -> Result<I::Item, ProgramError>
*)
Instance run_next_account_info
    (I : Set) `{Link I}
    (iter : Ref.t Pointer.Kind.MutRef I) :
  Run.Trait
    lib.next_account_info [] [Φ I] [φ iter]
    (Result.t (Ref.t Pointer.Kind.Ref AccountInfo.t) ProgramError.t).
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_next_account_info.
