Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.links.result.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.host.sload.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.

Definition sload
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  popn_top_macro interpreter 0
    (fun interpreter => (interpreter, host)) (fun _ index_stub interpreter =>
  let index := index_stub.(RefStub.projection) interpreter.(Interpreter.stack) in
  let spec_id :=
    IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  let target_address :=
    IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.target_address)
      interpreter.(Interpreter.input) in
  let gas :=
    if Impl_SpecId.is_enabled_in spec_id SpecId.BERLIN then
      WARM_STORAGE_READ_COST
    else if Impl_SpecId.is_enabled_in spec_id SpecId.ISTANBUL then
      ISTANBUL_SLOAD_GAS
    else if Impl_SpecId.is_enabled_in spec_id SpecId.TANGERINE then
      200
    else
      50 in
  gas_macro interpreter
    gas
    (fun interpreter => (interpreter, host)) (fun interpreter =>
  if Impl_SpecId.is_enabled_in spec_id SpecId.BERLIN then
    let skip_cold :=
      interpreter.(Interpreter.gas).(Gas.remaining).(Integer.value) <?
      COLD_SLOAD_COST_ADDITIONAL.(Integer.value) in
    let '(value_result, host) :=
      IHost.(Host.sload_skip_cold_load) host target_address index skip_cold in
    match value_result with
    | Result.Ok value =>
        if value.(StateLoad.is_cold) then
          gas_macro interpreter COLD_SLOAD_COST_ADDITIONAL
            (fun interpreter => (interpreter, host)) (fun interpreter =>
          let stack :=
            index_stub.(RefStub.injection)
              interpreter.(Interpreter.stack)
              value.(StateLoad.data) in
          (interpreter <| Interpreter.stack := stack |>, host))
        else
          let stack :=
            index_stub.(RefStub.injection)
              interpreter.(Interpreter.stack)
              value.(StateLoad.data) in
          (interpreter <| Interpreter.stack := stack |>, host)
    | Result.Err LoadError.ColdLoadSkipped =>
        (halt_oog interpreter, host)
    | Result.Err LoadError.DBError =>
        (halt_fatal interpreter, host)
    end
  else
  let '(value_opt, host) := IHost.(Host.sload) host target_address index in
  match value_opt with
  | None =>
      (halt_fatal interpreter, host)
  | Some value =>
  let stack :=
    index_stub.(RefStub.injection)
      interpreter.(Interpreter.stack)
      value.(StateLoad.data) in
  (interpreter <| Interpreter.stack := stack |>, host)
  end)).

Lemma sload_eq
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
  let result := sload interpreter host in
  {{
    SimulateM.eval_f
      (run_sload run_InterpreterTypes_for_WIRE run_Host_for_H context)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
Admitted.
