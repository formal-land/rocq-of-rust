Require Import links.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.common.

(*
pub enum TxKind {
    Create,
    Call(Address),
}
*)
Module TxKind.
  RocqOfRustLinkEnum "alloy_primitives::common::TxKind" :=
  | Create
  | Call (address : Address.t)
  .
End TxKind.
Export (hints) TxKind.
