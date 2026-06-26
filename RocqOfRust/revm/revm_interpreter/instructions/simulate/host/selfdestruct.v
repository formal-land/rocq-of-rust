Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.result.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.host.selfdestruct.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.instructions.simulate.utility.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.

Definition selfdestruct
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
  popn_macro interpreter 1 (fun interpreter => (interpreter, host)) (fun arr interpreter =>
    let '⟬ target_u256 ⟭ := arr.(array.value) in
    let target := Impl_IntoAddress_for_U256.into_address target_u256 in
    let spec_id :=
      IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id)
        interpreter.(Interpreter.runtime_flag) in
    gas_macro interpreter
      (calc.static_selfdestruct_cost spec_id)
      (fun interpreter => (interpreter, host)) (fun interpreter =>
    let skip_cold_load :=
      i[interpreter.(Interpreter.gas).(Gas.remaining)] <?
        i[calc.selfdestruct_cold_beneficiary_cost spec_id] in
    let address :=
      IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.target_address)
        interpreter.(Interpreter.input) in
    let '(result, host) := IHost.(Host.selfdestruct) host address target skip_cold_load in
    match result with
    | Result.Ok state_load =>
      let state_load_ref : '& (StateLoad.t SelfDestructResult.t) :=
        Ref.immediate Pointer.Kind.Ref state_load in
      gas_macro interpreter
        (calc.dyn_selfdestruct_cost spec_id state_load_ref)
        (fun interpreter => (interpreter, host)) (fun interpreter =>
      let is_london := Impl_SpecId.is_enabled_in spec_id SpecId.LONDON in
      let should_refund :=
        negb is_london && negb state_load.(StateLoad.data).(SelfDestructResult.previously_destroyed) in
      let interpreter :=
        if should_refund then
          let gas := Impl_Gas.record_refund interpreter.(Interpreter.gas) constants.SELFDESTRUCT_REFUND in
          interpreter <| Interpreter.gas := gas |>
        else
          interpreter in
      (halt interpreter instruction_result.InstructionResult.SelfDestruct, host))
    | Result.Err LoadError.ColdLoadSkipped =>
      (halt_oog interpreter, host)
    | Result.Err LoadError.DBError =>
      (halt_fatal interpreter, host)
    end))
  ).

Lemma selfdestruct_eq
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
  let result := selfdestruct interpreter host in
  {{
    SimulateM.eval_f
      (run_selfdestruct run_InterpreterTypes_for_WIRE run_Host_for_H context)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
Admitted.
