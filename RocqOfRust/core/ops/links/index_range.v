Require Import links.RocqOfRust.
Require Import core.ops.index_range.

(*
pub struct IndexRange {
    start: usize,
    end: usize,
}
*)
Module IndexRange.
  RocqOfRustLinkRecord "core::ops::index_range::IndexRange" := {
    start : usize;
    end_ : usize
  }.
End IndexRange.
Export (hints) IndexRange.
