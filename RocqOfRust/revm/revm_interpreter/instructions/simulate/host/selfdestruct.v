Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.instructions.links.host.selfdestruct.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.instructions.simulate.utility.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.

Definition selfdestruct
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  let set_result
      (interpreter : Interpreter.t WIRE WIRE_types)
      (result : InstructionResult.t) :=
    let control :=
      IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        result in
    interpreter <| Interpreter.control := control |> in
  popn_macro interpreter 1 (fun interpreter => (interpreter, host)) (fun arr interpreter =>
    let '{| ArrayPair.x := target_u256 |} := arr.(array.value) in
    let target := Impl_IntoAddress_for_U256.into_address target_u256 in
    let address :=
      IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.target_address)
        interpreter.(Interpreter.input) in
    let '(result, host) := IHost.(Host.selfdestruct) host address target in
    match result with
    | Some _ =>
      (set_result interpreter instruction_result.InstructionResult.SelfDestruct, host)
    | None =>
      (set_result interpreter instruction_result.InstructionResult.FatalExternalError, host)
    end
  ).

Lemma selfdestruct_eq
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
        (run_selfdestruct run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host)
        [interpreter; host]%stack 🌲
      (
        Output.Success tt,
        stack'
      )
    }}.
Admitted.
