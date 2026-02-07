Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.instructions.links.host.sload.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.

Definition sload
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  let set_fatal (interpreter : Interpreter.t WIRE WIRE_types) :=
    let control :=
      IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.FatalExternalError in
    interpreter <| Interpreter.control := control |> in
  popn_top_macro interpreter 0 (fun interpreter => (interpreter, host)) (fun _ top interpreter =>
    let target :=
      IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.target_address)
        interpreter.(Interpreter.input) in
    let index := top.(RefStub.projection) interpreter.(Interpreter.stack) in
    let '(result, host) := IHost.(Host.sload) host target index in
    match result with
    | Some state_load =>
      let stack := top.(RefStub.injection) interpreter.(Interpreter.stack) state_load.(StateLoad.data) in
      (interpreter <| Interpreter.stack := stack |>, host)
    | None =>
      (set_fatal interpreter, host)
    end
  ).

Lemma sload_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_Host_for_H : Host.Run H H_types)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref (A := H) 1 in
  exists stack' : Stack.t,
    {{
      SimulateM.eval_f
        (run_sload run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host)
        [interpreter; host]%stack 🌲
      (
        Output.Success tt,
        stack'
      )
    }}.
Admitted.
