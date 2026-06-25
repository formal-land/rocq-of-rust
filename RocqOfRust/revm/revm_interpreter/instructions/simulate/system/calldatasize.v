Require Import simulate.RocqOfRust.
Require Import core.slice.simulate.mod.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.interpreter_action.simulate.call_inputs.
Require Import revm.revm_interpreter.instructions.links.system.calldatasize.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.links.lib.
Require Import ruint.simulate.from.

Definition calldatasize
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  let input :=
    IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.input)
      .(RefStub.projection) interpreter.(Interpreter.input) in
  let length : usize := call_inputs.CallInput.len input in
  push_macro interpreter
    (Impl_Uint.from length)
    id id
  .

Lemma calldatasize_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref (A := H) 1 in
  let context := {|
    instruction_context.InstructionContext.interpreter := ref_interpreter;
    instruction_context.InstructionContext.host := ref_host;
  |} in
    {{
      SimulateM.eval_f
        (run_calldatasize run_InterpreterTypes_for_WIRE context)
        [interpreter; host]%stack 🌲
      (
        Output.Success tt,
        [calldatasize interpreter; host]%stack
      )
    }}.
Proof.
  with_strategy transparent [run_calldatasize] unfold calldatasize, run_calldatasize; cbn.
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply call_inputs.CallInput.len_eq with
      (self :=
        IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.input)
          .(RefStub.projection) interpreter.(Interpreter.input)).
    cbn.
    refine (@CanRead.Mutable
      _ _
      Pointer.Kind.Ref
      [interpreter; host]%stack
      (IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.input)
        .(RefStub.projection) interpreter.(Interpreter.input))
      _
      (@Stack.CanAccess.Mutable
        _ _
        [interpreter; host]%stack
        0
        (Interpreter.t WIRE WIRE_types)
        (@Stack.Nth.ConsZero (Interpreter.t WIRE WIRE_types) interpreter [host]%stack)
        _ _ _ _)
      _).
    reflexivity.
  }
  s. {
    s_apply Impl_Uint.from_eq.
  }
  push_macro_eq InterpreterTypesEq.
  s.
Qed.
