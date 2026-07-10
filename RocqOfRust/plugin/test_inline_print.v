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

Module DebugLinkedGeneric.
  RocqOfRustLinkLinkedGenericEnum "debug::LinkedGeneric" [ T ] :=
  | RefValue (value : ('& T))
  | OwnedValue (value : T)
  .
End DebugLinkedGeneric.

Print DebugLinkedGeneric.t.
Print DebugLinkedGeneric.IsLink.
Print DebugLinkedGeneric.IsOfTy.
Check DebugLinkedGeneric.IsOfValueWith_RefValue.
Check DebugLinkedGeneric.IsOfValue_RefValue.
Check DebugLinkedGeneric.SubPointer.get_RefValue_0.

Module DebugGenericRecord.
  RocqOfRustLinkGenericRecord "debug::GenericRecord" [ T ] := {
    payload : T;
    flag : bool
  }.
End DebugGenericRecord.

Print DebugGenericRecord.t.
Print DebugGenericRecord.IsLink.
Print DebugGenericRecord.IsOfTy.
Check DebugGenericRecord.IsOfValueWith.
Check DebugGenericRecord.IsOfValue.
Check DebugGenericRecord.SubPointer.get_payload.
