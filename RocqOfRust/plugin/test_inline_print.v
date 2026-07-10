Require Import links.RocqOfRust.
Require Import revm.revm_interpreter.links.interpreter_types.

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

Module DebugGenericPair.
  RocqOfRustLinkGenericEnum "debug::GenericPair" [ T, E ] :=
  | Left (value : T)
  | Right (err : E)
  .
End DebugGenericPair.

Print DebugGenericPair.t.
Print DebugGenericPair.IsLink.
Print DebugGenericPair.IsOfTy.
Check DebugGenericPair.IsOfValueWith_Left.
Check DebugGenericPair.IsOfValue_Left.
Check DebugGenericPair.SubPointer.get_Left_0.

Module DebugLinkedGeneric.
  RocqOfRustLinkGenericEnum "debug::LinkedGeneric" [ T ] :=
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

Module DebugTupleStruct.
  RocqOfRustLinkTupleStruct "debug::TupleStruct" := {
    value : u8
  }.
End DebugTupleStruct.

Print DebugTupleStruct.t.
Print DebugTupleStruct.IsLink.
Print DebugTupleStruct.IsOfTy.
Check DebugTupleStruct.IsOfValueWith.
Check DebugTupleStruct.IsOfValue.
Check DebugTupleStruct.SubPointer.get_value.

Module DebugTupleRecord.
  RocqOfRustLinkTupleRecord := {
    left : u64;
    right : bool
  }.
End DebugTupleRecord.

Print DebugTupleRecord.t.
Print DebugTupleRecord.IsLink.
Print DebugTupleRecord.IsOfTy.
Check DebugTupleRecord.IsOfValueWith.
Check DebugTupleRecord.IsOfValue.
Check DebugTupleRecord.SubPointer.get_left.

Module DebugInterpreterTypesRecord.
  RocqOfRustLinkInterpreterTypesRecord "debug::InstructionContext" [ H, WIRE ] WIRE_types := {
    interpreter : ('&mut WIRE);
    host : ('&mut H)
  }.
End DebugInterpreterTypesRecord.

Check DebugInterpreterTypesRecord.t.
Check DebugInterpreterTypesRecord.IsLink.
Check DebugInterpreterTypesRecord.of_ty.
Check DebugInterpreterTypesRecord.SubPointer.get_interpreter.

Module DebugInterpreterTypesRecordNoValueArgs.
  RocqOfRustLinkInterpreterTypesRecordNoValueArgs "debug::Interpreter" [ WIRE ] WIRE_types := {
    stack : WIRE_types.(InterpreterTypes.Types.Stack);
    gas : u64
  }.
End DebugInterpreterTypesRecordNoValueArgs.

Check DebugInterpreterTypesRecordNoValueArgs.t.
Check DebugInterpreterTypesRecordNoValueArgs.IsLink.
Check DebugInterpreterTypesRecordNoValueArgs.of_ty.
Check DebugInterpreterTypesRecordNoValueArgs.SubPointer.get_stack.
