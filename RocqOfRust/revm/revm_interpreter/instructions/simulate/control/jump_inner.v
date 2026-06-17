Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.control.jump_inner.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_specification.simulate.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.cmp.
Require Import ruint.simulate.from.
Require Import ruint.simulate.lib.

Definition jump_inner
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (target : aliases.U256.t) :
    Interpreter.t WIRE WIRE_types :=
  as_usize_or_fail_macro interpreter target (Some instruction_result.InstructionResult.InvalidJump)
    id (fun target interpreter =>
  let '(is_valid, bytecode) :=
    IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode).(Jumps.is_valid_legacy_jump)
      interpreter.(Interpreter.bytecode)
      target in
  let interpreter := interpreter <| Interpreter.bytecode := bytecode |> in
  if negb is_valid then
    let control :=
      IInterpreterTypes
        .(InterpreterTypes.LoopControl_for_Control)
        .(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.InvalidJump in
    interpreter <| Interpreter.control := control |>
  else
    let bytecode :=
      IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode).(Jumps.absolute_jump)
        interpreter.(Interpreter.bytecode)
        target in
    interpreter <| Interpreter.bytecode := bytecode |>
  ).

Lemma jump_inner_eq
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (target : aliases.U256.t)
    (stack : Stack.t) :
  let ref_interpreter := make_ref 0 in
  {{
    SimulateM.eval_f
      (run_jump_inner run_InterpreterTypes_for_WIRE ref_interpreter target)
      (interpreter :: stack)%stack 🌲
    (
      Output.Success tt,
      (jump_inner interpreter target :: stack)%stack
    )
  }}.
Proof.
  intros.
  apply Run.remove_extra_stack1.
  with_strategy transparent [run_jump_inner] unfold jump_inner, run_jump_inner; cbn.
  as_usize_or_fail_macro_eq InterpreterTypesEq.
  s. {
    apply InterpreterTypesEq.
  }
  s.
  destruct _.(Jumps.is_valid_legacy_jump) as [is_valid bytecode], is_valid; cbn.
  { s. {
      apply InterpreterTypesEq.
    }
    s.
  }
  { s. {
      apply InterpreterTypesEq.
    }
    s.
  }
Qed.
