Require Import links.RocqOfRust.
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
  RocqOfRustLinkEnum "revm_context_interface::transaction::transaction_type::TransactionType" :=
  | Legacy
  | Eip2930
  | Eip1559
  | Eip4844
  | Eip7702
  | Custom
  .
End TransactionType.
Export (hints) TransactionType.

Module Impl_PartialEq_for_TransactionType.
  Definition Self : Set := TransactionType.t.

  Instance run : PartialEq.Run Self Self.
  Admitted.
End Impl_PartialEq_for_TransactionType.
Export (hints) Impl_PartialEq_for_TransactionType.
