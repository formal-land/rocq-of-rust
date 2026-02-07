Require Import simulate.RocqOfRust.
Require Import alloc.links.raw_vec.
Require Import alloc.vec.links.mod.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.log.links.mod.
Require Import bytes.links.bytes.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.instructions.links.host.log.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.

Definition log
    (N : usize)
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  popn_macro interpreter 2 (fun interpreter => (interpreter, host)) (fun _arr interpreter =>
    let target :=
      IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.target_address)
        interpreter.(Interpreter.input) in
    let topics : Vec.t aliases.U256.t Global.t := {|
      Vec.buf := {| RawVec.value := [] |};
      Vec.len := 0;
    |} in
    let data : Bytes.t := {|
      Bytes.value := {| bytes.Bytes.value := [] |};
    |} in
    let log' : Log.t LogData.t := {|
      Log.address := target;
      Log.data := {|
        LogData.topics := topics;
        LogData.data := data;
      |};
    |} in
    let host := IHost.(Host.log) host log' in
    (interpreter, host)
  ).

Lemma log_eq
    (N : usize)
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
        (run_log (N := N) run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host)
        [interpreter; host]%stack 🌲
      (
        Output.Success tt,
        stack'
      )
    }}.
Admitted.
