Require Import links.RocqOfRust.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.instruction_context.

Module InstructionContext.
  RocqOfRustLinkInterpreterTypesRecord
    "revm_interpreter::instruction_context::InstructionContext" [ H, WIRE ] WIRE_types := {
    interpreter : ('&mut (Interpreter.t WIRE WIRE_types));
    host : ('&mut H)
  }.
End InstructionContext.

#[export] Existing Instance InstructionContext.IsLink.
