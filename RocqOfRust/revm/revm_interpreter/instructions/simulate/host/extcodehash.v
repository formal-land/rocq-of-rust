Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import core.convert.simulate.mod.
Require Import core.links.array.
Require Import core.links.result.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_context_interface.simulate.journaled_state.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.host.extcodehash.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.instructions.simulate.utility.
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
  let spec_id :=
    IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  let set_hash account interpreter host :=
    let code_hash :=
      if account.(AccountInfoLoad.is_empty) then
        Impl_FixedBytes.ZERO
      else
        account_info_load_code_hash account in
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack)
        (Impl_IntoU256_for_B256.into_u256 code_hash) in
    (interpreter <| Interpreter.stack := stack |>, host) in
  if Impl_SpecId.is_enabled_in spec_id SpecId.BERLIN then
    gas_macro interpreter WARM_STORAGE_READ_COST
      (fun interpreter => (interpreter, host)) (fun interpreter =>
    let cold_account_access_cost_additional :=
      BinOp.Wrap.sub COLD_ACCOUNT_ACCESS_COST WARM_STORAGE_READ_COST in
    let skip_cold_load :=
      interpreter.(Interpreter.gas).(Gas.remaining).(Integer.value) <?
      cold_account_access_cost_additional.(Integer.value) in
    let '(account_result, host) :=
      IHost.(Host.load_account_info_skip_cold_load) host address true skip_cold_load in
    match account_result with
    | Result.Ok account =>
      if account.(AccountInfoLoad.is_cold) then
        gas_macro interpreter cold_account_access_cost_additional
          (fun interpreter => (interpreter, host)) (fun interpreter =>
        set_hash account interpreter host)
      else
        set_hash account interpreter host
    | Result.Err LoadError.ColdLoadSkipped =>
      (halt_oog interpreter, host)
    | Result.Err LoadError.DBError =>
      (halt_fatal interpreter, host)
    end)
  else
    gas_macro interpreter
      (if Impl_SpecId.is_enabled_in spec_id SpecId.ISTANBUL then
        700
      else
        400)
      (fun interpreter => (interpreter, host))
      (fun interpreter =>
    let '(account_result, host) :=
      IHost.(Host.load_account_info_skip_cold_load) host address true false in
    match account_result with
    | Result.Ok account => set_hash account interpreter host
    | Result.Err _ => (halt_fatal interpreter, host)
    end))).

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
  let context := {|
    instruction_context.InstructionContext.interpreter := ref_interpreter;
    instruction_context.InstructionContext.host := ref_host;
  |} in
  let result := extcodehash interpreter host in
  {{
    SimulateM.eval_f
      (run_extcodehash run_InterpreterTypes_for_WIRE run_Host_for_H context)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
  with_strategy transparent [run_extcodehash] unfold extcodehash, run_extcodehash; cbn.
  check_macro_eq InterpreterTypesEq.
  popn_top_macro_eq InterpreterTypesEq.
  s. {
    apply Impl_IntoAddress_for_U256.into_address_eq.
  }
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply Impl_SpecId.is_enabled_in_eq.
  }
  destruct Impl_SpecId.is_enabled_in; cbn.
  { gas_macro_eq idtac.
    s. {
      apply Impl_Gas.remaining_interpreter_eq.
    }
    s. {
      apply constants.COLD_ACCOUNT_ACCESS_COST_ADDITIONAL_eq.
    }
    s. {
      apply HostEq.
    }
    remember (IHost.(Host.load_account_info_skip_cold_load) host
      (Impl_IntoAddress_for_U256.into_address (t0.(RefStub.projection) s))
      true
      (i[Impl_Gas.remaining s0] <? (2600 - 100) mod 2 ^ 64)) as account_load.
    destruct account_load as [[account|err] host_after]; cbn.
    1: destruct account.(AccountInfoLoad.is_cold); cbn.
    all: admit.
  }
  { s. {
      apply Impl_SpecId.is_enabled_in_eq.
    }
    destruct Impl_SpecId.is_enabled_in; cbn.
    { gas_macro_eq idtac.
      s. {
        apply HostEq.
      }
      destruct _.(Host.load_account_info_skip_cold_load) as [[account|err] ?host]; cbn.
      1: destruct account.(AccountInfoLoad.is_empty); cbn.
      all: admit.
    }
    all: admit.
  }
Admitted.
