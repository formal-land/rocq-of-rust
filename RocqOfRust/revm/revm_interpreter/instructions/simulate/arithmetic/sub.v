Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.simulate.option.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.arithmetic.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.links.lib.
Require Import ruint.simulate.add.

Definition sub
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  popn_top_macro interpreter 1 id (fun arr top interpreter =>
  let '⟬ op1 ⟭ := arr.(array.value) in
  let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
  let stack :=
    top.(RefStub.injection)
      interpreter.(Interpreter.stack) (Impl_Uint.wrapping_sub op1 op2) in
  interpreter
    <| Interpreter.stack := stack |>
  ).

Lemma sub_eq
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
  let context := {|
    instruction_context.InstructionContext.interpreter := ref_interpreter;
    instruction_context.InstructionContext.host := ref_host;
  |} in
  {{
    SimulateM.eval_f
      (run_sub run_InterpreterTypes_for_WIRE context)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        sub interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  with_strategy transparent [run_sub] unfold sub, run_sub; cbn.
  unfold popn_top_macro.
  s; [
    apply InterpreterTypesEq
      .(InterpreterTypes.Eq.StackTrait_for_Stack)
      .(StackTrait.Eq.len)
  |].
  repeat s.
  destruct (_ <? _) eqn:H_len; cbn.
  { s; [
      eapply halt_underflow_eq;
      try exact InterpreterTypesEq
    |].
    repeat s.
  }
  eapply Run.Call; [
    apply InterpreterTypesEq
      .(InterpreterTypes.Eq.StackTrait_for_Stack)
      .(StackTrait.Eq.popn_top)
  |].
  cbn.
  destruct
    (IInterpreterTypes
      .(InterpreterTypes.StackTrait_for_Stack)
      .(StackTrait.popn_top) {| Integer.value := 1 |} interpreter.(Interpreter.stack))
    as [[[arr top] |] stack] eqn:H_popn_top;
    cbn.
  { eapply Run.Call; [
      eapply Impl_Option.unwrap_unchecked_eq;
      reflexivity
    |].
    cbn.
    match goal with
    | array : array.t aliases.U256.t _ |- _ =>
      destruct array as [[op1 []]]
    end.
    s; [
      apply Impl_Uint.wrapping_sub_eq
    |].
    s.
    change
      (IInterpreterTypes
        .(InterpreterTypes.StackTrait_for_Stack)
        .(StackTrait.popn_top) 1 interpreter.(Interpreter.stack))
      with
      (IInterpreterTypes
        .(InterpreterTypes.StackTrait_for_Stack)
        .(StackTrait.popn_top) {| Integer.value := 1 |} interpreter.(Interpreter.stack)).
    rewrite H_popn_top.
    reflexivity.
  }
  pose proof (
    StackTrait.popn_top_some_of_len
      IInterpreterTypes.(InterpreterTypes.StackTrait_for_Stack)
      interpreter.(Interpreter.stack)
      {| Integer.value := 1 |}
      H_len
  ) as (? & ? & ? & H_some).
  rewrite H_popn_top in H_some.
  discriminate.
Qed.
