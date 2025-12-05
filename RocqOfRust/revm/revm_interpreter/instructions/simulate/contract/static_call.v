Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.instructions.links.contract.static_call.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import revm.revm_specification.simulate.hardfork.

Definition check_macro {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (min : SpecId.t)
    (k : Interpreter.t WIRE WIRE_types -> Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  if
    Impl_SpecId.is_enabled_in
      (IInterpreterTypes
          .(InterpreterTypes.RuntimeFlag)
          .(SRuntimeFlag.spec_id)
        interpreter.(Interpreter.runtime_flag)
      )
      min
  then
    k interpreter
  else
    let control :=
      IInterpreterTypes
          .(InterpreterTypes.Loop)
          .(Loop.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.NotActivated in
    interpreter
      <| Interpreter.control := control |>.

Lemma static_call_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (run_Host_for_H : Host.Run H H_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    SimulateM.eval_f (
      run_static_call
        run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host
      )
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [
        check_macro interpreter SpecId.BYZANTIUM (fun interpreter =>
          interpreter
        );
        host
      ]%stack
    )
  }}.
Proof.
  intros.
  destruct InterpreterTypesEq as [[] [] []].
  unfold run_static_call; cbn.
  unfold check_macro; cbn.
  eapply Run.Call. {
    apply spec_id.
  }
  cbn.
  eapply Run.Call. {
    apply Impl_SpecId.is_enabled_in_eq.
  }
  cbn.
  eapply Run.Call. {
    apply Run.Pure.
  }
  cbn.
  eapply Run.Call. {
    apply Run.Pure.
  }
  cbn.
  destruct Impl_SpecId.is_enabled_in; cbn.
  { admit. }
  { eapply Run.Call. {
      apply (set_instruction_result _ _ instruction_result.InstructionResult.NotActivated).
    }
    cbn.
    apply Run.Pure.
  }
Admitted.
Global Opaque run_static_call.
