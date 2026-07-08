Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.links.result.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.host.sstore.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter.
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
  let spec_id :=
    IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  if (Impl_SpecId.is_enabled_in spec_id SpecId.ISTANBUL)
      && (i[Impl_Gas.remaining interpreter.(Interpreter.gas)] <=? i[constants.CALL_STIPEND]) then
    (halt interpreter instruction_result.InstructionResult.ReentrancySentryOOG, host)
  else
  gas_macro interpreter
    (calc.static_sstore_cost spec_id)
    (fun interpreter => (interpreter, host)) (fun interpreter =>
  if Impl_SpecId.is_enabled_in spec_id SpecId.BERLIN then
    let skip_cold :=
      i[Impl_Gas.remaining interpreter.(Interpreter.gas)] <?
      COLD_SLOAD_COST_ADDITIONAL.(Integer.value) in
    let '(result, host) :=
      IHost.(Host.sstore_skip_cold_load) host target index value skip_cold in
    match result with
    | Result.Ok state_load =>
        let vals_ref : '& SStoreResult.t :=
          Ref.immediate Pointer.Kind.Ref state_load.(StateLoad.data) in
        gas_macro interpreter
          (calc.dyn_sstore_cost spec_id vals_ref state_load.(StateLoad.is_cold))
          (fun interpreter => (interpreter, host)) (fun interpreter =>

        let refund := calc.sstore_refund spec_id vals_ref in
        let gas := Impl_Gas.record_refund interpreter.(Interpreter.gas) refund in
        (interpreter <| Interpreter.gas := gas |>, host))
    | Result.Err LoadError.ColdLoadSkipped =>
        (halt_oog interpreter, host)
    | Result.Err LoadError.DBError =>
        (halt_fatal interpreter, host)
    end
  else
    let '(result, host) := IHost.(Host.sstore) host target index value in
    match result with
    | Some state_load =>
        let vals_ref : '& SStoreResult.t :=
          Ref.immediate Pointer.Kind.Ref state_load.(StateLoad.data) in
        gas_macro interpreter
          (calc.dyn_sstore_cost spec_id vals_ref state_load.(StateLoad.is_cold))
          (fun interpreter => (interpreter, host)) (fun interpreter =>

        let refund := calc.sstore_refund spec_id vals_ref in
        let gas := Impl_Gas.record_refund interpreter.(Interpreter.gas) refund in
        (interpreter <| Interpreter.gas := gas |>, host))
    | None =>
        (halt_fatal interpreter, host)
    end))).

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
  let context := {|
    instruction_context.InstructionContext.interpreter := ref_interpreter;
    instruction_context.InstructionContext.host := ref_host;
  |} in
  let result := sstore interpreter host in
  {{
    SimulateM.eval_f
      (run_sstore run_InterpreterTypes_for_WIRE run_Host_for_H context)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
Admitted.
