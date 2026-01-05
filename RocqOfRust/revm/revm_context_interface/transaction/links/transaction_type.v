Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.links.cmp.

(*
pub enum TransactionType {
    Legacy,
    Eip2930,
    Eip1559,
    Eip4844,
    Eip7702,
    Custom,
}
*)
Module TransactionType.
  Inductive t : Set :=
  | Legacy
  | Eip2930
  | Eip1559
  | Eip4844
  | Eip7702
  | Custom.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::transaction::transaction_type::TransactionType";
    φ x :=
      match x with
      | Legacy => Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Legacy" [] [] []
      | Eip2930 => Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip2930" [] [] []
      | Eip1559 => Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip1559" [] [] []
      | Eip4844 => Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip4844" [] [] []
      | Eip7702 => Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip7702" [] [] []
      | Custom => Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Custom" [] [] []
      end;
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::transaction::transaction_type::TransactionType").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Global Instance IsOfValueWith_Legacy :
    OfValueWith.C t (Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Legacy" [] [] []) :=
  {
    value := Legacy;
    eq := eq_refl;
  }.

  Global Instance IsOfValueWith_Eip2930 :
    OfValueWith.C t (Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip2930" [] [] []) :=
  {
    value := Eip2930;
    eq := eq_refl;
  }.

  Global Instance IsOfValueWith_Eip1559 :
    OfValueWith.C t (Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip1559" [] [] []) :=
  {
    value := Eip1559;
    eq := eq_refl;
  }.

  Global Instance IsOfValueWith_Eip4844 :
    OfValueWith.C t (Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip4844" [] [] []) :=
  {
    value := Eip4844;
    eq := eq_refl;
  }.

  Global Instance IsOfValueWith_Eip7702 :
    OfValueWith.C t (Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip7702" [] [] []) :=
  {
    value := Eip7702;
    eq := eq_refl;
  }.

  Global Instance IsOfValueWith_Custom :
    OfValueWith.C t (Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Custom" [] [] []) :=
  {
    value := Custom;
    eq := eq_refl;
  }.

  Definition of_value_Legacy :
    OfValue.t (Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Legacy" [] [] []).
  Proof. econstructor; smpl of_value. Defined.
  Smpl Add apply of_value_Legacy : of_value.

  Definition of_value_Eip2930 :
    OfValue.t (Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip2930" [] [] []).
  Proof. econstructor; smpl of_value. Defined.
  Smpl Add apply of_value_Eip2930 : of_value.

  Definition of_value_Eip1559 :
    OfValue.t (Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip1559" [] [] []).
  Proof. econstructor; smpl of_value. Defined.
  Smpl Add apply of_value_Eip1559 : of_value.

  Definition of_value_Eip4844 :
    OfValue.t (Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip4844" [] [] []).
  Proof. econstructor; smpl of_value. Defined.
  Smpl Add apply of_value_Eip4844 : of_value.

  Definition of_value_Eip7702 :
    OfValue.t (Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip7702" [] [] []).
  Proof. econstructor; smpl of_value. Defined.
  Smpl Add apply of_value_Eip7702 : of_value.

  Definition of_value_Custom :
    OfValue.t (Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Custom" [] [] []).
  Proof. econstructor; smpl of_value. Defined.
  Smpl Add apply of_value_Custom : of_value.
End TransactionType.

Module Impl_PartialEq_for_TransactionType.
  Definition Self : Set := TransactionType.t.

  Instance run : PartialEq.Run Self Self.
  Admitted.
End Impl_PartialEq_for_TransactionType.
