Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.simulations.M.
Require Import RocqOfRust.lib.lib.

Module IndexKind.
  Inductive t : Set :=
  | ModuleHandle
  | StructHandle
  | FunctionHandle
  | FieldHandle
  | FriendDeclaration
  | FunctionInstantiation
  | FieldInstantiation
  | StructDefinition
  | StructDefInstantiation
  | FunctionDefinition
  | FieldDefinition
  | Signature
  | Identifier
  | AddressIdentifier
  | ConstantPool
  | LocalPool
  | CodeDefinition
  | TypeParameter
  | MemberCount
  .
End IndexKind.