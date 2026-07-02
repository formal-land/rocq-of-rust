Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.simulate.option.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.host.blockhash.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.instructions.simulate.utility.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.links.lib.
Require Import ruint.simulate.add.
Require Import ruint.simulate.bytes.
Require Import ruint.simulate.lib.

Definition blockhash
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  popn_top_macro interpreter 0
    (fun interpreter => (interpreter, host)) (fun _ number_stub interpreter =>

  let requested_number := number_stub.(RefStub.projection) interpreter.(Interpreter.stack) in
  let block_number := IHost.(Host.block_number) host in
  match Impl_Uint.checked_sub block_number requested_number with
  | None =>
    let stack :=
      number_stub.(RefStub.injection) interpreter.(Interpreter.stack) Impl_Uint.ZERO in
    (interpreter <| Interpreter.stack := stack |>, host)
  | Some diff =>
    let diff := as_u64_saturated_macro diff in
    if i[diff] =? 0 then
      let stack :=
        number_stub.(RefStub.injection) interpreter.(Interpreter.stack) Impl_Uint.ZERO in
      (interpreter <| Interpreter.stack := stack |>, host)
    else if i[diff] <=? 256 then
      let requested_number := as_u64_saturated_macro requested_number in
      let '(hash_opt, host) := IHost.(Host.block_hash) host requested_number in
      match hash_opt with
      | None =>
        (halt_fatal interpreter, host)
      | Some hash =>
        let stack :=
          number_stub.(RefStub.injection)
            interpreter.(Interpreter.stack)
            (Impl_Uint.from_be_bytes hash.(fixed_FixedBytes.FixedBytes.value)) in
        (interpreter <| Interpreter.stack := stack |>, host)
      end
    else
      let stack :=
        number_stub.(RefStub.injection) interpreter.(Interpreter.stack) Impl_Uint.ZERO in
      (interpreter <| Interpreter.stack := stack |>, host)
  end).

Lemma blockhash_eq
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
  let result := blockhash interpreter host in
  {{
    SimulateM.eval_f
      (run_blockhash run_InterpreterTypes_for_WIRE run_Host_for_H context)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
Admitted.
