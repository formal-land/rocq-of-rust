Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.links.result.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_context_interface.simulate.journaled_state.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.host.balance.
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
  let set_balance account interpreter host :=
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack)
        (account_info_load_balance account) in
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
      IHost.(Host.load_account_info_skip_cold_load) host address false skip_cold_load in
    match account_result with
    | Result.Ok account =>
      if account.(AccountInfoLoad.is_cold) then
        gas_macro interpreter cold_account_access_cost_additional
          (fun interpreter => (interpreter, host)) (fun interpreter =>
        set_balance account interpreter host)
      else
        set_balance account interpreter host
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
      (fun interpreter => (interpreter, host))
      (fun interpreter =>
    let '(account_result, host) :=
      IHost.(Host.load_account_info_skip_cold_load) host address false false in
    match account_result with
    | Result.Ok account => set_balance account interpreter host
    | Result.Err _ => (halt_fatal interpreter, host)
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
    instruction_context.InstructionContext.interpreter := ref_interpreter;
    instruction_context.InstructionContext.host := ref_host;
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
Proof.
  intros.
  subst result.
  with_strategy transparent [run_balance] unfold balance, run_balance; cbn.
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
  destruct Impl_SpecId.is_enabled_in eqn:H_berlin; cbn.
  - gas_macro_eq idtac.
    s. {
      apply Impl_Gas.remaining_interpreter_eq.
    }
    s. {
      apply constants.COLD_ACCOUNT_ACCESS_COST_ADDITIONAL_eq.
    }
    s. {
      apply HostEq.
    }
    remember
      (IHost.(Host.load_account_info_skip_cold_load) host
        (Impl_IntoAddress_for_U256.into_address (t0.(RefStub.projection) s))
        false
        (i[Impl_Gas.remaining s0] <? (2600 - 100) mod 2 ^ 64))
      as account_load eqn:H_balance_result.
    destruct account_load as [[account|load_error] host_after]; cbn.
    + symmetry in H_balance_result.
      destruct account as [account_info account_is_cold account_is_empty]; cbn in *.
      destruct account_is_cold; cbn.
      * setoid_rewrite H_balance_result.
        cbn.
        s. {
          apply constants.COLD_ACCOUNT_ACCESS_COST_ADDITIONAL_eq.
        }
        cbn.
        unfold gas_macro.
        s. {
          apply Impl_Gas.record_cost_interpreter_eq.
        }
        destruct Impl_Gas.record_cost; cbn.
        -- eapply Run.Call. {
             apply Run.Pure.
           }
           cbn.
           admit.
        -- eapply Run.Call. {
             apply Run.Pure.
           }
           cbn.
           s. {
             eapply halt_oog_eq;
             exact InterpreterTypesEq.
           }
           cbn.
           setoid_rewrite H_balance_result.
           cbn.
           apply Run.Pure.
      * setoid_rewrite H_balance_result.
        cbn.
        admit.
    + symmetry in H_balance_result.
      destruct load_error; cbn.
      * setoid_rewrite H_balance_result.
        cbn.
        admit.
      * setoid_rewrite H_balance_result.
        cbn.
        admit.
  - admit.
Admitted.
