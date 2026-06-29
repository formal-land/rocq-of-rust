Require Import simulate.RocqOfRust.
Require Import alloc.links.borrow.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.links.result.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.host.balance.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.instructions.simulate.utility.
Require Import revm.revm_state.links.account_info.
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
Require Import ruint.links.lib.

Definition set_top_to_account_balance
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (top : RefStub.t WIRE_types.(InterpreterTypes.Types.Stack) aliases.U256.t)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (account_load : AccountInfoLoad.t) :
    Interpreter.t WIRE WIRE_types :=
  let account := Cow.deref account_load.(AccountInfoLoad.account) in
  let stack :=
    top.(RefStub.injection)
      interpreter.(Interpreter.stack)
      account.(AccountInfo.balance) in
  interpreter <| Interpreter.stack := stack |>.

Definition balance
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  popn_top_macro interpreter 0
    (fun interpreter => (interpreter, host)) (fun _ top interpreter =>
  let address :=
    Impl_IntoAddress_for_U256.into_address
      (top.(RefStub.projection) interpreter.(Interpreter.stack)) in
  let spec_id :=
    IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  if Impl_SpecId.is_enabled_in spec_id SpecId.BERLIN then
    gas_macro interpreter constants.WARM_STORAGE_READ_COST
      (fun interpreter => (interpreter, host)) (fun interpreter =>
    let skip_cold_load :=
      i[interpreter.(Interpreter.gas).(Gas.remaining)] <?
        i[constants.COLD_ACCOUNT_ACCESS_COST_ADDITIONAL] in
    let '(account_result, host) :=
      IHost.(Host.load_account_info_skip_cold_load)
        host address false skip_cold_load in
    match account_result with
    | Result.Ok account_load =>
      if account_load.(AccountInfoLoad.is_cold) then
        gas_macro interpreter constants.COLD_ACCOUNT_ACCESS_COST_ADDITIONAL
          (fun interpreter => (interpreter, host)) (fun interpreter =>
        (set_top_to_account_balance top interpreter account_load, host))
      else
        (set_top_to_account_balance top interpreter account_load, host)
    | Result.Err LoadError.ColdLoadSkipped =>
      (halt_oog interpreter, host)
    | Result.Err LoadError.DBError =>
      (halt_fatal interpreter, host)
    end)
  else
    gas_macro interpreter
      (if Impl_SpecId.is_enabled_in spec_id SpecId.ISTANBUL then
        700
      else if Impl_SpecId.is_enabled_in spec_id SpecId.TANGERINE then
        400
      else
        20)
      (fun interpreter => (interpreter, host)) (fun interpreter =>
    let '(account_result, host) :=
      IHost.(Host.load_account_info_skip_cold_load)
        host address false false in
    match account_result with
    | Result.Ok account_load =>
      (set_top_to_account_balance top interpreter account_load, host)
    | Result.Err _ =>
      (halt_fatal interpreter, host)
    end)).

Lemma balance_eq
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
    InstructionContext.interpreter := ref_interpreter;
    InstructionContext.host := ref_host;
  |} in
  let result := balance interpreter host in
  {{
    SimulateM.eval_f
      (run_balance run_InterpreterTypes_for_WIRE run_Host_for_H context)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Admitted.
