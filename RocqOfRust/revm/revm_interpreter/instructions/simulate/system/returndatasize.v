Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import bytes.simulate.bytes.
Require Import core.slice.simulate.mod.
Require Import revm.revm_interpreter.instructions.links.system.returndatasize.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.from.

Definition returndatasize
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  check_macro interpreter SpecId.BYZANTIUM id (fun interpreter =>
  let return_data :=
    IInterpreterTypes.(InterpreterTypes.ReturnData_for_ReturnData).(ReturnData.buffer)
      .(RefStub.projection) interpreter.(Interpreter.return_data) in
  let length : usize := Impl_Bytes.len return_data.(Bytes.value) in
  push_macro interpreter
    (Impl_Uint.from length)
    id id
  ).

Lemma returndatasize_eq
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
        (run_returndatasize run_InterpreterTypes_for_WIRE context)
        [interpreter; host]%stack 🌲
      (
        Output.Success tt,
        [returndatasize interpreter; host]%stack
      )
    }}.
Proof.
  with_strategy transparent [run_returndatasize] unfold returndatasize, run_returndatasize; cbn.
  check_macro_eq InterpreterTypesEq.
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply alloy_primitives.bytes.simulate.mod.Impl_Deref_for_Bytes.Eq.I.
  }
  s. {
    pose proof bytes.simulate.bytes.Impl_Bytes.len_eq as H_apply.
    s_apply H_apply.
  }
  s. {
    s_apply Impl_Uint.from_eq.
  }
  push_macro_eq InterpreterTypesEq.
  s.
Qed.
