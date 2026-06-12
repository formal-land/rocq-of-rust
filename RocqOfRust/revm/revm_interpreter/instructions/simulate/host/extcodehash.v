Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import core.convert.simulate.mod.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_context_interface.simulate.journaled_state.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.instructions.links.host.extcodehash.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.instructions.simulate.utility.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import revm.revm_specification.simulate.hardfork.

Definition extcodehash
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  check_macro interpreter SpecId.CONSTANTINOPLE
    (fun interpreter => (interpreter, host)) (fun interpreter =>
  popn_top_macro interpreter 0 (fun interpreter => (interpreter, host)) (fun _ top interpreter =>
  let address :=
    Impl_IntoAddress_for_U256.into_address
      (top.(RefStub.projection) interpreter.(Interpreter.stack)) in
  let '(code_hash_opt, host) := IHost.(Host.code_hash) host address in
  match code_hash_opt with
  | None =>
    let control :=
      IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.FatalExternalError in
    (interpreter <| Interpreter.control := control |>, host)
  | Some code_hash =>
  let '(code_hash, load) := Impl_Eip7702CodeLoad.into_components code_hash in
  let spec_id :=
    IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  gas_macro interpreter
    (if Impl_SpecId.is_enabled_in spec_id SpecId.BERLIN then
      calc.warm_cold_cost_with_delegation load
    else if Impl_SpecId.is_enabled_in spec_id SpecId.ISTANBUL then
      700
    else
      400)
    (fun interpreter => (interpreter, host)) (fun interpreter =>
  let stack :=
    top.(RefStub.injection)
      interpreter.(Interpreter.stack)
      (Impl_IntoU256_for_B256.into_u256 code_hash) in
  (interpreter <| Interpreter.stack := stack |>, host))
  end)).

Lemma extcodehash_eq
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
  let result := extcodehash interpreter host in
  {{
    SimulateM.eval_f
      (run_extcodehash run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
Admitted.
