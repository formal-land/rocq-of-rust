Require Import links.RocqOfRust.
Require Import alloc.borrow.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.bytes.links.mod.
Require Import core.links.option.
Require Import core.ops.links.function.
Require Import core.ops.links.deref.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_context_interface.journaled_state.
Require Import ruint.links.lib.

(*
pub struct StateLoad<T> {
    pub data: T,
    pub is_cold: bool,
}
*)
Module StateLoad.
  RocqOfRustLinkGenericRecord "revm_context_interface::journaled_state::StateLoad" [ T ] := {
    data : T;
    is_cold : bool
  }.
End StateLoad.
Export (hints) StateLoad.

(*
impl<T> Deref for StateLoad<T> {
    type Target = T;
*)
Module Impl_Deref_for_StateLoad.
  Definition Self (T : Set) `{Link T} : Set :=
    StateLoad.t T.

  Instance run_deref (T : Set) `{Link T} (self : '& (Self T)) :
    Run.Trait
      (journaled_state.Impl_core_ops_deref_Deref_for_revm_context_interface_journaled_state_StateLoad_T.deref (Φ T))
      [] [] [ φ self ] ('& T).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_deref.

  Instance method_deref (T : Set) `{Link T} : Deref.Method_deref (Self T) T.
  Proof.
    econstructor.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply journaled_state.Impl_core_ops_deref_Deref_for_revm_context_interface_journaled_state_StateLoad_T.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run (T : Set) `{Link T} : Deref.Run (Self T) T :=
  {}.
End Impl_Deref_for_StateLoad.
Export (hints) Impl_Deref_for_StateLoad.

Module Impl_StateLoad.
  Definition Self (T : Set) `{Link T} : Set :=
    StateLoad.t T.

  Instance run_new (T : Set) `{Link T} (data : T) (is_cold : bool) :
    Run.Trait
      (journaled_state.Impl_revm_context_interface_journaled_state_StateLoad_T.new (Φ T))
      [] [] [ φ data; φ is_cold ] (Self T).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_new.
End Impl_StateLoad.
Export (hints) Impl_StateLoad.

(*
pub struct Eip7702CodeLoad<T> {
    pub state_load: StateLoad<T>,
    pub is_delegate_account_cold: Option<bool>,
}
*)
Module Eip7702CodeLoad.
  RocqOfRustLinkGenericRecord "revm_context_interface::journaled_state::Eip7702CodeLoad" [ T ] := {
    state_load : (StateLoad.t T);
    is_delegate_account_cold : (option bool)
  }.
End Eip7702CodeLoad.
Export (hints) Eip7702CodeLoad.

(*
pub struct AccountLoad {
    pub load: Eip7702CodeLoad<()>,
    pub is_empty: bool,
}
*)
Module AccountLoad.
  Record t : Set := {
    load : Eip7702CodeLoad.t unit;
    is_empty : bool;
  }.

  Instance IsLink : Link t :=
  {
    Φ := Ty.path "revm_context_interface::journaled_state::AccountLoad";
    φ x :=
      Value.StructRecord "revm_context_interface::journaled_state::AccountLoad" [] [] [
        ("load", φ x.(load));
        ("is_empty", φ x.(is_empty))
      ];
  }.
  
  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::journaled_state::AccountLoad").
  Proof.
    eapply OfTy.Make with (A := t).
    reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with load load' is_empty is_empty' :
    load' = φ load ->
    is_empty' = φ is_empty ->
    Value.StructRecord "revm_context_interface::journaled_state::AccountLoad" [] [] [
      ("load", load');
      ("is_empty", is_empty')
    ] = φ (Build_t load is_empty).
  Proof.
    now intros; subst.
  Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value (load : Eip7702CodeLoad.t unit) load' (is_empty : bool) is_empty' :
    load' = φ load ->
    is_empty' = φ is_empty ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::journaled_state::AccountLoad" [] [] [
        ("load", load');
        ("is_empty", is_empty')
      ]
    ).
  Proof.
    econstructor; apply of_value_with; eassumption.
  Defined.
  Smpl Add apply of_value : of_value.

  Module SubPointer.
    Definition get_load : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::AccountLoad" "load") :=
    {|
      SubPointer.Runner.projection x := Some x.(load);
      SubPointer.Runner.injection x y := Some (x <| load := y |>);
    |}.

    Lemma get_load_is_valid :
      SubPointer.Runner.Valid.t get_load.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_load_is_valid : run_sub_pointer.

    Definition get_is_empty : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::AccountLoad" "is_empty") :=
    {|
      SubPointer.Runner.projection x := Some x.(is_empty);
      SubPointer.Runner.injection x y := Some (x <| is_empty := y |>);
    |}.

    Lemma get_is_empty_is_valid :
      SubPointer.Runner.Valid.t get_is_empty.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_is_empty_is_valid : run_sub_pointer.
  End SubPointer.
End AccountLoad.
Export (hints) AccountLoad.

Module Cow.
  RocqOfRustLinkGenericEnum "alloc::borrow::Cow" [ T ] :=
  | Borrowed (value : ('& T))
  | Owned (value : T)
  .
End Cow.
Export (hints) Cow.

Module AccountInfo.
  Record t : Set := {
    balance : aliases.U256.t;
    nonce : u64;
    code_hash : aliases.B256.t;
    code : option Bytecode.t;
  }.

  Instance IsLink : Link t := {
    Φ := Ty.path "revm_state::account_info::AccountInfo";
    φ x :=
      Value.StructRecord "revm_state::account_info::AccountInfo" [] [] [
        ("balance", φ x.(balance));
        ("nonce", φ x.(nonce));
        ("code_hash", φ x.(code_hash));
        ("code", φ x.(code))
      ];
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_state::account_info::AccountInfo").
  Proof.
    eapply OfTy.Make with (A := t); reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with
      balance balance'
      nonce nonce'
      code_hash code_hash'
      code code' :
    balance' = φ balance ->
    nonce' = φ nonce ->
    code_hash' = φ code_hash ->
    code' = φ code ->
    Value.StructRecord "revm_state::account_info::AccountInfo" [] [] [
      ("balance", balance');
      ("nonce", nonce');
      ("code_hash", code_hash');
      ("code", code')
    ] = φ (Build_t balance nonce code_hash code).
  Proof.
    now intros; subst.
  Qed.
  Smpl Add apply of_value_with : of_value.

  Module SubPointer.
    Definition get_balance : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_state::account_info::AccountInfo" "balance") :=
    {|
      SubPointer.Runner.projection x := Some x.(balance);
      SubPointer.Runner.injection x y := Some (x <| balance := y |>);
    |}.

    Lemma get_balance_is_valid :
      SubPointer.Runner.Valid.t get_balance.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_balance_is_valid : run_sub_pointer.

    Definition get_nonce : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_state::account_info::AccountInfo" "nonce") :=
    {|
      SubPointer.Runner.projection x := Some x.(nonce);
      SubPointer.Runner.injection x y := Some (x <| nonce := y |>);
    |}.

    Lemma get_nonce_is_valid :
      SubPointer.Runner.Valid.t get_nonce.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_nonce_is_valid : run_sub_pointer.

    Definition get_code_hash : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_state::account_info::AccountInfo" "code_hash") :=
    {|
      SubPointer.Runner.projection x := Some x.(code_hash);
      SubPointer.Runner.injection x y := Some (x <| code_hash := y |>);
    |}.

    Lemma get_code_hash_is_valid :
      SubPointer.Runner.Valid.t get_code_hash.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_code_hash_is_valid : run_sub_pointer.

    Definition get_code : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_state::account_info::AccountInfo" "code") :=
    {|
      SubPointer.Runner.projection x := Some x.(code);
      SubPointer.Runner.injection x y := Some (x <| code := y |>);
    |}.

    Lemma get_code_is_valid :
      SubPointer.Runner.Valid.t get_code.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_code_is_valid : run_sub_pointer.
  End SubPointer.
End AccountInfo.
Export (hints) AccountInfo.

Module Impl_Deref_for_Cow.
  Definition Self (T : Set) `{Link T} : Set :=
    Cow.t T.

  Instance run_deref (T : Set) `{Link T} (self : '& (Self T)) :
    Run.Trait
      (borrow.Impl_core_ops_deref_Deref_where_core_marker_Sized_B_where_alloc_borrow_ToOwned_B_for_alloc_borrow_Cow_B.deref (Φ T))
      [] [] [ φ self ] ('& T).
  Admitted.
  Global Opaque run_deref.

  Instance method_deref (T : Set) `{Link T} : Deref.Method_deref (Self T) T.
  Proof.
    econstructor.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply borrow.Impl_core_ops_deref_Deref_where_core_marker_Sized_B_where_alloc_borrow_ToOwned_B_for_alloc_borrow_Cow_B.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run (T : Set) `{Link T} : Deref.Run (Self T) T :=
  {}.
End Impl_Deref_for_Cow.
Export (hints) Impl_Deref_for_Cow.

(*
pub struct AccountInfoLoad<'a> {
    pub account: Cow<'a, AccountInfo>,
    pub is_cold: bool,
    pub is_empty: bool,
}
*)
Module AccountInfoLoad.
  Record t : Set := {
    account : Cow.t AccountInfo.t;
    is_cold : bool;
    is_empty : bool;
  }.

  Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::journaled_state::AccountInfoLoad";
    φ x :=
      Value.StructRecord "revm_context_interface::journaled_state::AccountInfoLoad" [] [] [
        ("account", φ x.(account));
        ("is_cold", φ x.(is_cold));
        ("is_empty", φ x.(is_empty))
      ];
  }.

  Definition of_ty :
    OfTy.t (Ty.path "revm_context_interface::journaled_state::AccountInfoLoad").
  Proof.
    eapply OfTy.Make with (A := t); reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with account account' is_cold is_cold' is_empty is_empty' :
    account' = φ account ->
    is_cold' = φ is_cold ->
    is_empty' = φ is_empty ->
    Value.StructRecord "revm_context_interface::journaled_state::AccountInfoLoad" [] [] [
      ("account", account');
      ("is_cold", is_cold');
      ("is_empty", is_empty')
    ] = φ (Build_t account is_cold is_empty).
  Proof.
    now intros; subst.
  Qed.
  Smpl Add apply of_value_with : of_value.

  Module SubPointer.
    Definition get_account : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::AccountInfoLoad" "account") :=
    {|
      SubPointer.Runner.projection x := Some x.(account);
      SubPointer.Runner.injection x y := Some (x <| account := y |>);
    |}.

    Lemma get_account_is_valid :
      SubPointer.Runner.Valid.t get_account.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_account_is_valid : run_sub_pointer.

    Definition get_is_cold : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::AccountInfoLoad" "is_cold") :=
    {|
      SubPointer.Runner.projection x := Some x.(is_cold);
      SubPointer.Runner.injection x y := Some (x <| is_cold := y |>);
    |}.

    Lemma get_is_cold_is_valid :
      SubPointer.Runner.Valid.t get_is_cold.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_is_cold_is_valid : run_sub_pointer.

    Definition get_is_empty : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::AccountInfoLoad" "is_empty") :=
    {|
      SubPointer.Runner.projection x := Some x.(is_empty);
      SubPointer.Runner.injection x y := Some (x <| is_empty := y |>);
    |}.

    Lemma get_is_empty_is_valid :
      SubPointer.Runner.Valid.t get_is_empty.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_is_empty_is_valid : run_sub_pointer.
  End SubPointer.
End AccountInfoLoad.
Export (hints) AccountInfoLoad.

Module Impl_AccountInfoLoad.
  Definition Self : Set :=
    AccountInfoLoad.t.

  Instance run_into_state_load {F O : Set} `{Link F} `{Link O}
      (Run_FnOnce_for_F : function.FnOnce.Run F (OneElementTuple.t (Cow.t AccountInfo.t)) O)
      (self : Self) (f : F) :
    Run.Trait
      journaled_state.Impl_revm_context_interface_journaled_state_AccountInfoLoad.into_state_load
      [] [ Φ F; Φ O ] [ φ self; φ f ]
      (StateLoad.t O).
  Proof.
    constructor.
    run_symbolic.
    eapply Run.CallPrimitiveGetTraitMethod.
    { exact Run_FnOnce_for_F.(function.FnOnce.method_call_once).(function.FnOnce.call_once_is_method).(IsTraitMethod.Make). }
    run_symbolic.
  Defined.
  Global Opaque run_into_state_load.
End Impl_AccountInfoLoad.
Export (hints) Impl_AccountInfoLoad.

Module Impl_Deref_for_AccountInfoLoad.
  Definition Self : Set :=
    AccountInfoLoad.t.

  Instance run_deref (self : '& Self) :
    Run.Trait
      journaled_state.Impl_core_ops_deref_Deref_for_revm_context_interface_journaled_state_AccountInfoLoad.deref
      [] [] [ φ self ] ('& AccountInfo.t).
  Proof.
    constructor.
    run_symbolic.
    eapply Run.CallPrimitiveGetTraitMethod.
    { exact (Impl_Deref_for_Cow.method_deref AccountInfo.t).(deref.Deref.deref_is_method).(IsTraitMethod.Make). }
    run_symbolic.
  Defined.
  Global Opaque run_deref.

  Instance method_deref : Deref.Method_deref Self AccountInfo.t.
  Proof.
    econstructor.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply journaled_state.Impl_core_ops_deref_Deref_for_revm_context_interface_journaled_state_AccountInfoLoad.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run : Deref.Run Self AccountInfo.t :=
  {}.
End Impl_Deref_for_AccountInfoLoad.
Export (hints) Impl_Deref_for_AccountInfoLoad.
