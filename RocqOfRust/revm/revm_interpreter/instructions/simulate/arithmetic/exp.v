Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.instructions.links.arithmetic.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.pow.

Definition exp
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  let spec_id :=
    IInterpreterTypes
        .(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
        .(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  popn_top_macro interpreter 1 id (fun arr top interpreter =>
  let '⟬ op1 ⟭ := arr.(array.value) in
  let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
  gas_or_fail_macro interpreter (exp_cost spec_id op2) id (fun interpreter =>
  let stack :=
    top.(RefStub.injection)
      interpreter.(Interpreter.stack) (Impl_Uint.pow op1 op2) in
  interpreter
    <| Interpreter.stack := stack |>
  )).

Lemma exp_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_host : '&mut H := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_exp run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        exp IInterpreterTypes interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  unfold exp.
  s. {
    apply InterpreterTypesEq.
  }
  popn_top_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t aliases.U256.t _ |- _ =>
    destruct array as [[op1 []]]
  end.
  s. {
    apply exp_cost_eq.
  }
  unfold gas_macro.
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply Impl_Gas.record_cost_eq.
  }
  destruct Impl_Gas.record_cost.
  { s. {
      apply Impl_Uint.pow_eq.
    }
    s.
  }
  { s. {
      apply InterpreterTypesEq.
    }
    s.
  }
Qed.
