Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.links.mod.
Require Import bytes.links.bytes.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.instructions.links.host.extcodesize.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.instructions.simulate.utility.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import ruint.links.lib.

Definition extcodesize
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
    let address :=
      Impl_IntoAddress_for_U256.into_address
        (top.(RefStub.projection) interpreter.(Interpreter.stack)) in
    let '(result, host) := IHost.(Host.code) host address in
    match result with
    | Some code_load =>
      let code := code_load.(Eip7702CodeLoad.state_load).(StateLoad.data) in
      let size : aliases.U256.t := {|
        Uint.value := Z.of_nat (List.length code.(Bytes.value).(bytes.Bytes.value))
      |} in
      let stack := top.(RefStub.injection) interpreter.(Interpreter.stack) size in
      (interpreter <| Interpreter.stack := stack |>, host)
    | None =>
      (set_fatal interpreter, host)
    end
  ).

Lemma extcodesize_eq
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
        (run_extcodesize run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host)
        [interpreter; host]%stack 🌲
      (
        Output.Success tt,
        stack'
      )
    }}.
Admitted.
