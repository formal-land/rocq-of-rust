Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.simulate.default.
Require Import core.simulate.option.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.instructions.links.tx_info.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import ruint.simulate.lib.

Module Sim_Default_for_U256.
  Instance I : Default.C aliases.U256.t := {|
    Default.default := Impl_Uint.ZERO;
  |}.

  Module Eq.
    Instance I :
      @Default.Eq.C
        aliases.U256.t
        _
        Impl_Default_for_U256.run
        Sim_Default_for_U256.I.
    Proof.
      constructor; intros.
      s. {
        apply Impl_Uint.ZERO_eq.
      }
      s.
    Qed.
  End Eq.
  Export (hints) Eq.
End Sim_Default_for_U256.
Export (hints) Sim_Default_for_U256.

Definition blob_hash
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  check_macro interpreter SpecId.CANCUN (fun interpreter => (interpreter, host)) (fun interpreter =>
  popn_top_macro interpreter 0
    (fun interpreter => (interpreter, host)) (fun _ index_stub interpreter =>
  let index := index_stub.(RefStub.projection) interpreter.(Interpreter.stack) in
  let index_usize := as_usize_saturated_macro index in
  let '(hash_opt, host) := IHost.(Host.blob_hash) host index_usize in
  let hash :=
    match hash_opt with
    | Some hash => hash
    | None => Impl_Uint.ZERO
    end in
  let stack := index_stub.(RefStub.injection) interpreter.(Interpreter.stack) hash in
  (interpreter <| Interpreter.stack := stack |>, host))).

Lemma blob_hash_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_Host_for_H : Host.Run H H_types)
    `{IInterpreterTypes : !InterpreterTypes.C WIRE_types}
    `{InterpreterTypesEq :
      !InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes}
    `{IHost : !Host.C H H_types}
    `{HostEq : !Host.Eq.t IHost}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref (A := H) 1 in
  let context := {|
    instruction_context.InstructionContext.interpreter := ref_interpreter;
    instruction_context.InstructionContext.host := ref_host;
  |} in
  let result := blob_hash interpreter host in
  {{
    SimulateM.eval_f
      (run_blob_hash run_InterpreterTypes_for_WIRE run_Host_for_H context)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
  intros.
  subst result.
  with_strategy transparent [run_blob_hash] unfold blob_hash, run_blob_hash; cbn.
  check_macro_eq InterpreterTypesEq.
  popn_top_macro_eq InterpreterTypesEq.
  eapply Run.Call; [
    eapply Impl_Option.unwrap_unchecked_eq;
    reflexivity
  |].
  cbn.
  match goal with
  | top : RefStub.t _ aliases.U256.t,
    stack_after : WIRE_types.(InterpreterTypes.Types.Stack) |- _ =>
      eapply Run.Let with
        (result := (
          Output.Success
            (as_usize_saturated_macro
              (top.(RefStub.projection) stack_after)),
          _
        ))
  end.
  -
    as_usize_saturated_macro_eq.
  -
    set (index := as_usize_saturated_macro (t0.(RefStub.projection) s)).
    match goal with
    | |- context [IHost.(Host.blob_hash) host index] =>
        destruct (IHost.(Host.blob_hash) host index) as [hash_opt host_after] eqn:?
    end.
    s. {
      eapply Run.Call.
      {
        pose proof
          (HostEq.(Host.Eq.blob_hash)
            (interpreter<|Interpreter.stack:= s|>)
            host
            index
            ([tt; tt; index]%stack)) as H_blob_hash.
        cbn [SimulateM.eval_f] in H_blob_hash.
        exact H_blob_hash.
      }
      s.
    }
    rewrite Heqp; cbn.
    s. {
      eapply Impl_Option.unwrap_or_default_eq.
    }
    cbn.
    destruct hash_opt; s.
Qed.
