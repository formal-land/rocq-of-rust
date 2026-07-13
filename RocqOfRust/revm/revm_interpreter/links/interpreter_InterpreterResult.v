Require Import links.RocqOfRust.
Require Import alloy_primitives.bytes.links.mod.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm_interpreter.links.gas.
Require Import revm.revm_interpreter.interpreter.

(*
pub struct InterpreterResult {
    pub result: InstructionResult,
    pub output: Bytes,
    pub gas: Gas,
}
*)
Module InterpreterResult.
  RocqOfRustLinkRecord "revm_interpreter::interpreter::InterpreterResult" := {
    result : InstructionResult.t;
    output : Bytes.t;
    gas : Gas.t
  }.
End InterpreterResult.
Export (hints) InterpreterResult.

(* impl InterpreterResult { *)
Module Impl_InterpreterResult.
  Definition Self : Set :=
    InterpreterResult.t.

  Instance run_new
      (result : InstructionResult.t)
      (output : Bytes.t)
      (gas : Gas.t) :
    Run.Trait
      interpreter.Impl_revm_interpreter_interpreter_InterpreterResult.new
        [] [] [ φ result; φ output; φ gas ]
      Self.
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_new.
End Impl_InterpreterResult.
Export (hints) Impl_InterpreterResult.
