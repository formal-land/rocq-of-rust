Require Import links.RocqOfRust.

Module DebugOrdering.
  RocqOfRustLinkEnum "core::cmp::Ordering" :=
  | Less
  | Equal
  | Greater
  .
End DebugOrdering.

Print DebugOrdering.t.
Print DebugOrdering.IsLink.
Print DebugOrdering.IsOfTy.
Print DebugOrdering.IsOfValueWith_Less.
Print DebugOrdering.IsOfValue_Less.
Print DebugOrdering.SubPointer.
