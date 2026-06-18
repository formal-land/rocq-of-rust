Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.host.sstore.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.

Definition sstore
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  require_non_staticcall_macro interpreter
    (fun interpreter => (interpreter, host)) (fun interpreter =>

  popn_macro interpreter 2 (fun interpreter => (interpreter, host)) (fun arr interpreter =>
  let '⟬ index; value ⟭ := arr.(array.value) in
  let target :=
    IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.target_address)
      interpreter.(Interpreter.input) in
  let '(result, host) := IHost.(Host.sstore) host target index value in
  match result with
  | None =>
    let control :=
      IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.FatalExternalError in
    (interpreter <| Interpreter.control := control |>, host)
  | Some state_load =>

  let spec_id :=
    IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  let gas :=
    IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.gas)
      .(RefStub.projection) interpreter.(Interpreter.control) in
  if (Impl_SpecId.is_enabled_in spec_id SpecId.ISTANBUL)
      && (i[gas.(Gas.remaining)] <=? i[constants.CALL_STIPEND]) then
    let control :=
      IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.ReentrancySentryOOG in
    (interpreter <| Interpreter.control := control |>, host)
  else
  let spec_id :=
    IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  let vals_ref : '& SStoreResult.t :=
    Ref.immediate Pointer.Kind.Ref state_load.(StateLoad.data) in
  gas_macro interpreter
    (calc.sstore_cost spec_id vals_ref state_load.(StateLoad.is_cold))
    (fun interpreter => (interpreter, host)) (fun interpreter =>

  let spec_id :=
    IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  let refund := calc.sstore_refund spec_id vals_ref in
  let gas :=
    IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.gas)
      .(RefStub.projection) interpreter.(Interpreter.control) in
  let gas := Impl_Gas.record_refund gas refund in
  let control :=
    IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.gas)
      .(RefStub.injection) interpreter.(Interpreter.control) gas in
  (interpreter <| Interpreter.control := control |>, host))
  end)).

Lemma sstore_eq
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
  let result := sstore interpreter host in
  {{
    SimulateM.eval_f
      (run_sstore run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
  with_strategy transparent [run_sstore] unfold sstore, run_sstore; cbn.
  require_non_staticcall_macro_eq InterpreterTypesEq.
  popn_macro_eq InterpreterTypesEq.
  match goal with
  | arr : array.t aliases.U256.t _ |- _ =>
    destruct arr as [[index [value []]]]
  end.
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply HostEq.
  }
  destruct _.(Host.sstore) as [[state_load|] ?host]; cbn. 2: {
    s. {
      apply InterpreterTypesEq.
    }
    s.
  }
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply Impl_SpecId.is_enabled_in_eq.
  }
  destruct Impl_SpecId.is_enabled_in; cbn.
  { s. {
      apply InterpreterTypesEq.
    }
    s. {
      apply Impl_Gas.remaining_eq.
    }
    s.
    destruct (_ <=? _); cbn.
    { s. {
        apply InterpreterTypesEq.
      }
      s.
    }
    { gas_macro_eq ltac:(
        s; [apply InterpreterTypesEq|];
        s; [apply calc.sstore_cost_eq|]
      ).
      s. {
        apply InterpreterTypesEq.
      }
      s. {
        apply InterpreterTypesEq.
      }
      s. {
        apply calc.sstore_refund_eq.
      }
      s. {
        apply Impl_Gas.record_refund_eq.
      }
      s.
    }
  }
  { gas_macro_eq ltac:(
      s; [apply InterpreterTypesEq|];
      s; [apply calc.sstore_cost_eq|]
    ).
    s. {
      apply InterpreterTypesEq.
    }
    s. {
      apply InterpreterTypesEq.
    }
    s. {
      apply calc.sstore_refund_eq.
    }
    s. {
      apply Impl_Gas.record_refund_eq.
    }
    s.
  }
Qed.
