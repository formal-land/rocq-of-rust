Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.interpreter_InterpreterResult.
Require Import revm.revm_interpreter.links.instruction_result.

Definition new_return
    (result : InstructionResult.t)
    (output : Bytes.t)
    (gas : Gas.t) :
    InterpreterAction.t :=
  InterpreterAction.Return {|
    InterpreterResult.result := result;
    InterpreterResult.output := output;
    InterpreterResult.gas := gas;
  |}.

Lemma new_return_eq
    (result : InstructionResult.t)
    (output : Bytes.t)
    (gas : Gas.t)
    (stack : Stack.t) :
  {{
    SimulateM.eval_f
      (Impl_InterpreterAction.run_new_return result output gas)
      stack 🌲
    (
      Output.Success (new_return result output gas),
      stack
    )
  }}.
Proof.
  with_strategy transparent [Impl_InterpreterAction.run_new_return]
    unfold new_return, Impl_InterpreterAction.run_new_return.
  cbn.
  s.
Qed.
