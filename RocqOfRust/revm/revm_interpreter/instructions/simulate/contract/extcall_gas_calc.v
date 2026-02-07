Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.simulate.address.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import core.num.simulate.mod.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.contract.extcall_gas_calc.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.simulate.from.
Require Import ruint.simulate.lib.

Definition extcall_gas_calc
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H)
    (target : Address.t)
    (transfers_value : bool) :
    option u64 * Interpreter.t WIRE WIRE_types * H :=
  match IHost.(Host.load_account_delegated) host target with
  | (None, host) =>
    let control :=
      IInterpreterTypes
          .(InterpreterTypes.LoopControl_for_Control)
          .(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.FatalExternalError in
    let interpreter :=
      interpreter
        <| Interpreter.control := control |> in
    (None, interpreter, host)
  | (Some account_load, host) =>

  let spec_id :=
    IInterpreterTypes
        .(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
        .(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  let call_cost := call_cost spec_id transfers_value account_load in
  gas_macro interpreter call_cost
    (fun interpreter => (None, interpreter, host)) (fun interpreter =>

  let gas :=
    IInterpreterTypes
        .(InterpreterTypes.LoopControl_for_Control)
        .(LoopControl.gas)
        .(RefStub.projection)
      interpreter.(Interpreter.control) in
  let gas_reduce : u64 :=
    {| Integer.value := Z.max (Impl_Gas.remaining gas /i 64).(Integer.value) 5000 |} in
  let gas_limit :=
    Impl_u64.saturating_sub (Impl_Gas.remaining gas) gas_reduce in

  if gas_limit.(Integer.value) <? MIN_CALLEE_GAS.(Integer.value) then
    push_macro interpreter (Impl_Uint.from (1 : u64))
      (fun interpreter => (None, interpreter, host)) (fun interpreter =>
    let return_data :=
      IInterpreterTypes
          .(InterpreterTypes.ReturnData_for_ReturnData)
          .(ReturnData.buffer_mut)
          .(RefStub.injection)
        interpreter.(Interpreter.return_data)
        Impl_Bytes.new in
    let interpreter :=
      interpreter
        <| Interpreter.return_data := return_data |> in
    (None, interpreter, host))
  else
    gas_macro interpreter gas_limit
      (fun interpreter => (None, interpreter, host)) (fun interpreter =>
    (Some gas_limit, interpreter, host))
  ) end.

Lemma extcall_gas_calc_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (run_Host_for_H : Host.Run H H_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (IHost : Host.C H H_types)
    (HostEq : Host.Eq.t IHost)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H)
    (target : Address.t)
    (transfers_value : bool) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    SimulateM.eval_f (
      run_extcall_gas_calc
        run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host target transfers_value
      )
      [interpreter; host]%stack 🌲
    let '(result, interpreter, host) := extcall_gas_calc interpreter host target transfers_value in
    (
      Output.Success result,
      [interpreter; host]%stack
    )
  }}.
Proof.
Admitted.
