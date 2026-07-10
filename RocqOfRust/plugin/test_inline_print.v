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

Module DebugGeneric.
  RocqOfRustLinkGenericEnum "debug::Generic" [ T ] :=
  | WithValue (value : T)
  | Empty
  .
End DebugGeneric.

Print DebugGeneric.t.
Print DebugGeneric.IsLink.
Print DebugGeneric.IsOfTy.
Check DebugGeneric.IsOfValueWith_WithValue.
Check DebugGeneric.IsOfValue_WithValue.
Check DebugGeneric.SubPointer.get_WithValue_0.
