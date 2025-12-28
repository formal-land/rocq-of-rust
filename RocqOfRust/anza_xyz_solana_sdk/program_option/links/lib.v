Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import anza_xyz_solana_sdk.program_option.lib.

(*
  pub enum COption<T> {
      None,
      Some(T),
  }
*)
Module COption.
  Inductive t (T : Set) : Set :=
  | None
  | Some (value : T).
  Arguments None {T}.
  Arguments Some {T}.

  Global Instance IsLink (T : Set) `{Link T} : Link (t T) := {
    Φ := Ty.apply (Ty.path "solana_program_option::COption") [] [Φ T];
    φ x :=
      match x with
      | None => Value.StructTuple "solana_program_option::COption::None" [] [Φ T] []
      | Some v => Value.StructTuple "solana_program_option::COption::Some" [] [Φ T] [φ v]
      end
  }.

  Definition of_ty T_ty :
    OfTy.t T_ty ->
    OfTy.t (Ty.apply (Ty.path "solana_program_option::COption") [] [T_ty]).
  Proof.
    intros [T].
    eapply OfTy.Make with (A := t T).
    subst.
    reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with_None (T : Set) `{Link T} :
    Value.StructTuple "solana_program_option::COption::None" [] [Φ T] [] = φ (@None T).
  Proof. reflexivity. Qed.
  Definition of_value_None T' :
    OfTy.t T' ->
    OfValue.t (Value.StructTuple "solana_program_option::COption::None" [] [T'] []).
  Proof.
    intros [T].
    eapply OfValue.Make with (A := t T) (value := None).
    subst.
    apply of_value_with_None.
  Defined.
  Smpl Add unshelve eapply of_value_None : of_value.

  Lemma of_value_with_Some (T : Set) `{Link T} (value : T) (value' : Value.t) :
    value' = φ value ->
    Value.StructTuple "solana_program_option::COption::Some" [] [Φ T] [value'] = φ (Some value).
  Proof. intros; subst; reflexivity. Qed.
  Smpl Add apply of_value_with_Some : of_value.
  Definition of_value_Some T' value'
     (H_T' : OfTy.t T')
     (value : OfTy.get_Set H_T') :
    value' = φ value ->
    OfValue.t (Value.StructTuple "solana_program_option::COption::Some" [] [T'] [value']).
  Proof.
    intros.
    destruct H_T' as [T].
    eapply OfValue.Make with (A := t T) (value := Some value).
    subst.
    now apply of_value_with_Some.
  Defined.
  Smpl Add unshelve eapply of_value_Some : of_value.

  Module SubPointer.
    Definition get_Some_0 (T : Set) `{Link T} : SubPointer.Runner.t (t T)
      (Pointer.Index.StructTuple "solana_program_option::COption::Some" 0) :=
    {|
      SubPointer.Runner.projection x :=
        match x with
        | Some v => Datatypes.Some v
        | None => Datatypes.None
        end;
      SubPointer.Runner.injection x y :=
        match x with
        | Some _ => Datatypes.Some (Some y)
        | None => Datatypes.None
        end;
    |}.

    Lemma get_Some_0_is_valid (T : Set) `{Link T} :
      SubPointer.Runner.Valid.t (get_Some_0 T).
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Some_0_is_valid : run_sub_pointer.
  End SubPointer.
End COption.

(* impl<T> COption<T> *)
Module Impl_COption.
  Definition Self (T : Set) : Set := COption.t T.

  (* pub fn is_some(&self) -> bool *)
  Instance run_is_some
      (T : Set) `{Link T}
      (self : Ref.t Pointer.Kind.Ref (Self T)) :
    Run.Trait
      (lib.Impl_solana_program_option_COption_T.is_some (Φ T)) [] [] [φ self]
      bool.
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_is_some.

  (* pub fn is_none(&self) -> bool *)
  Instance run_is_none
      (T : Set) `{Link T}
      (self : Ref.t Pointer.Kind.Ref (Self T)) :
    Run.Trait
      (lib.Impl_solana_program_option_COption_T.is_none (Φ T)) [] [] [φ self]
      bool.
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_is_none.

  (* pub fn unwrap(self) -> T *)
  Instance run_unwrap
      (T : Set) `{Link T}
      (self : Self T) :
    Run.Trait
      (lib.Impl_solana_program_option_COption_T.unwrap (Φ T)) [] [] [φ self]
      T.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_unwrap.

  (* pub fn unwrap_or(self, def: T) -> T *)
  Instance run_unwrap_or
      (T : Set) `{Link T}
      (self : Self T)
      (def : T) :
    Run.Trait
      (lib.Impl_solana_program_option_COption_T.unwrap_or (Φ T)) [] [] [φ self; φ def]
      T.
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_unwrap_or.
End Impl_COption.
