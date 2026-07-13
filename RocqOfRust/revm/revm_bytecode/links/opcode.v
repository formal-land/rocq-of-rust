Require Import links.RocqOfRust.
Require Import revm.revm_bytecode.opcode.

(* pub struct OpCode(u8); *)
Module OpCode.
  RocqOfRustLinkTupleStruct "revm_bytecode::opcode::OpCode" := {
    value : u8
  }.
End OpCode.
Export (hints) OpCode.
#[export] Existing Instance OpCode.IsLink.

Module Impl_OpCode.
  Instance run_STOP :
    Run.Trait
      opcode.Impl_revm_bytecode_opcode_OpCode.value_STOP [] [] []
      ('* OpCode.t).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_STOP.

  Instance run_ADD :
    Run.Trait
      opcode.Impl_revm_bytecode_opcode_OpCode.value_ADD [] [] []
      ('* OpCode.t).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_ADD.

  Instance run_BALANCE :
    Run.Trait
      opcode.Impl_revm_bytecode_opcode_OpCode.value_BALANCE [] [] []
      ('* OpCode.t).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_BALANCE.
End Impl_OpCode.

Instance run_STOP :
  Run.Trait
    opcode.value_STOP [] [] []
    ('* u8).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_STOP.

Instance run_ADD :
  Run.Trait
    opcode.value_ADD [] [] []
    ('* u8).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_ADD.

Instance run_BALANCE :
  Run.Trait
    opcode.value_BALANCE [] [] []
    ('* u8).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_BALANCE.
