Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.links.result.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.host.sload.
Require Import revm.revm_interpreter.instructions.simulate.macros.
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

Definition sload
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  popn_top_macro interpreter 0
    (fun interpreter => (interpreter, host)) (fun _ index_stub interpreter =>
  let index := index_stub.(RefStub.projection) interpreter.(Interpreter.stack) in
  let spec_id :=
    IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  let target_address :=
    IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.target_address)
      interpreter.(Interpreter.input) in
  let gas :=
    if Impl_SpecId.is_enabled_in spec_id SpecId.BERLIN then
      WARM_STORAGE_READ_COST
    else if Impl_SpecId.is_enabled_in spec_id SpecId.ISTANBUL then
      ISTANBUL_SLOAD_GAS
    else if Impl_SpecId.is_enabled_in spec_id SpecId.TANGERINE then
      200
    else
      50 in
  gas_macro interpreter
    gas
    (fun interpreter => (interpreter, host)) (fun interpreter =>
  if Impl_SpecId.is_enabled_in spec_id SpecId.BERLIN then
    let skip_cold :=
      i[Impl_Gas.remaining interpreter.(Interpreter.gas)] <?
      COLD_SLOAD_COST_ADDITIONAL.(Integer.value) in
    let '(value_result, host) :=
      IHost.(Host.sload_skip_cold_load) host target_address index skip_cold in
    match value_result with
    | Result.Ok value =>
        if value.(StateLoad.is_cold) then
          gas_macro interpreter COLD_SLOAD_COST_ADDITIONAL
            (fun interpreter => (interpreter, host)) (fun interpreter =>
          let stack :=
            index_stub.(RefStub.injection)
              interpreter.(Interpreter.stack)
              value.(StateLoad.data) in
          (interpreter <| Interpreter.stack := stack |>, host))
        else
          let stack :=
            index_stub.(RefStub.injection)
              interpreter.(Interpreter.stack)
              value.(StateLoad.data) in
          (interpreter <| Interpreter.stack := stack |>, host)
    | Result.Err LoadError.ColdLoadSkipped =>
        (halt_oog interpreter, host)
    | Result.Err LoadError.DBError =>
        (halt_fatal interpreter, host)
    end
  else
  let '(value_opt, host) := IHost.(Host.sload) host target_address index in
  match value_opt with
  | None =>
      (halt_fatal interpreter, host)
  | Some value =>
  let stack :=
    index_stub.(RefStub.injection)
      interpreter.(Interpreter.stack)
      value.(StateLoad.data) in
  (interpreter <| Interpreter.stack := stack |>, host)
  end)).

Lemma sload_eq
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
  let result := sload interpreter host in
  {{
    SimulateM.eval_f
      (run_sload run_InterpreterTypes_for_WIRE run_Host_for_H context)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
  intros.
  subst result.
  with_strategy transparent [run_sload] unfold sload, run_sload; cbn.
  popn_top_macro_eq InterpreterTypesEq.
  s. {
    apply InterpreterTypesEq.
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
      apply Impl_SpecId.is_enabled_in_eq.
    }
    rewrite H_berlin; cbn.
    s. {
      apply Impl_Gas.remaining_interpreter_eq.
    }
    s. {
      apply COLD_SLOAD_COST_ADDITIONAL_eq.
    }
    s. {
      apply HostEq.
    }
    destruct
      (IHost.(Host.sload_skip_cold_load) host
        (IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input)
          .(InputTraits.target_address) interpreter.(Interpreter.input))
        (t0.(RefStub.projection) s)
        (i[ Impl_Gas.remaining s0] <? (2100 - 100) mod 2 ^ 64))
      as [[value|load_error] host_after] eqn:H_sload_result; cbn.
    + destruct value as [value_data value_is_cold]; cbn in *.
      destruct value_is_cold; cbn.
      * get_can_access.
        setoid_rewrite H_sload_result.
        cbn.
        s. {
          apply COLD_SLOAD_COST_ADDITIONAL_eq.
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
           s.
           exact (f_equal snd H_sload_result).
        -- eapply Run.Call. {
             apply Run.Pure.
           }
           cbn.
           s. {
             eapply halt_oog_eq;
             exact InterpreterTypesEq.
           }
           cbn.
           setoid_rewrite H_sload_result.
           cbn.
           apply Run.Pure.
      * get_can_access.
        setoid_rewrite H_sload_result.
        cbn.
        s.
        exact (f_equal snd H_sload_result).
    + destruct load_error; cbn.
      * get_can_access.
        setoid_rewrite H_sload_result.
        cbn.
        get_can_access.
        setoid_rewrite H_sload_result.
        cbn.
        setoid_rewrite H_sload_result.
        cbn.
        s. {
          eapply halt_fatal_eq;
          exact InterpreterTypesEq.
        }
        cbn.
        apply Run.Pure.
      * get_can_access.
        setoid_rewrite H_sload_result.
        cbn.
        get_can_access.
        setoid_rewrite H_sload_result.
        cbn.
        s. {
          eapply halt_oog_eq;
          exact InterpreterTypesEq.
        }
        cbn.
        apply Run.PureEq.
        cbn.
        repeat f_equal.
        exact (f_equal snd H_sload_result).
  - s. {
      apply Impl_SpecId.is_enabled_in_eq.
    }
    s.
    destruct
      (Impl_SpecId.is_enabled_in
        (IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
          .(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag))
        SpecId.ISTANBUL) eqn:H_istanbul; cbn.
    + setoid_rewrite H_istanbul.
      cbn.
      eapply Run.Call. {
        apply ISTANBUL_SLOAD_GAS_eq.
      }
      cbn.
      unfold gas_macro.
      apply Run.LetUnfold.
      cbn.
      get_can_access.
      cbn.
      s. {
        apply Impl_Gas.record_cost_interpreter_eq.
      }
      destruct Impl_Gas.record_cost; cbn.
      * eapply Run.Call. {
          apply Run.Pure.
        }
        cbn.
        eapply Run.Call. {
          apply Run.Pure.
        }
        cbn.
        s. {
          apply Impl_SpecId.is_enabled_in_eq.
        }
        rewrite H_berlin; cbn.
        s. {
          apply HostEq.
        }
        destruct
          (IHost.(Host.sload) host
            (IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input)
              .(InputTraits.target_address) interpreter.(Interpreter.input))
            (t0.(RefStub.projection) s))
          as [[value|] host_after] eqn:H_sload_result; cbn.
        -- destruct value as [value_data value_is_cold]; cbn in *.
           setoid_rewrite H_sload_result.
           cbn.
           apply Run.LetUnfold.
           cbn.
           unshelve eapply Run.GetCanAccess.
           { cbn; repeat constructor. }
           cbn.
           apply Run.PureEq.
           cbn.
           repeat f_equal.
           exact (f_equal snd H_sload_result).
        -- setoid_rewrite H_sload_result.
           cbn.
           s. {
             eapply halt_fatal_eq;
             exact InterpreterTypesEq.
           }
           cbn.
           apply Run.PureEq.
           cbn.
           repeat f_equal.
           exact (f_equal snd H_sload_result).
      * eapply Run.Call. {
          apply Run.Pure.
        }
        cbn.
        s. {
          eapply halt_oog_eq;
          exact InterpreterTypesEq.
        }
        cbn.
        apply Run.Pure.
    + setoid_rewrite H_istanbul.
      cbn.
      s. {
        apply Impl_SpecId.is_enabled_in_eq.
      }
      s.
      destruct
        (Impl_SpecId.is_enabled_in
          (IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
            .(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag))
          SpecId.TANGERINE) eqn:H_tangerine; cbn.
      * setoid_rewrite H_tangerine.
        cbn.
        gas_macro_eq idtac.
        s. {
          apply Impl_SpecId.is_enabled_in_eq.
        }
        rewrite H_berlin; cbn.
        s. {
          apply HostEq.
        }
        destruct
          (IHost.(Host.sload) host
            (IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input)
              .(InputTraits.target_address) interpreter.(Interpreter.input))
            (t0.(RefStub.projection) s))
          as [[value|] host_after] eqn:H_sload_result; cbn.
        -- destruct value as [value_data value_is_cold]; cbn in *.
           setoid_rewrite H_sload_result.
           cbn.
           apply Run.LetUnfold.
           cbn.
           unshelve eapply Run.GetCanAccess.
           { cbn; repeat constructor. }
           cbn.
           apply Run.PureEq.
           cbn.
           repeat f_equal.
           exact (f_equal snd H_sload_result).
        -- setoid_rewrite H_sload_result.
           cbn.
           s. {
             eapply halt_fatal_eq;
             exact InterpreterTypesEq.
           }
           cbn.
           apply Run.PureEq.
           cbn.
           repeat f_equal.
           exact (f_equal snd H_sload_result).
      * setoid_rewrite H_tangerine.
        cbn.
        gas_macro_eq idtac.
        s. {
          apply Impl_SpecId.is_enabled_in_eq.
        }
        rewrite H_berlin; cbn.
        s. {
          apply HostEq.
        }
        destruct
          (IHost.(Host.sload) host
            (IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input)
              .(InputTraits.target_address) interpreter.(Interpreter.input))
            (t0.(RefStub.projection) s))
          as [[value|] host_after] eqn:H_sload_result; cbn.
        -- destruct value as [value_data value_is_cold]; cbn in *.
           setoid_rewrite H_sload_result.
           cbn.
           apply Run.LetUnfold.
           cbn.
           unshelve eapply Run.GetCanAccess.
           { cbn; repeat constructor. }
           cbn.
           apply Run.PureEq.
           cbn.
           repeat f_equal.
           exact (f_equal snd H_sload_result).
        -- setoid_rewrite H_sload_result.
           cbn.
           s. {
             eapply halt_fatal_eq;
             exact InterpreterTypesEq.
           }
           cbn.
           apply Run.PureEq.
           cbn.
           repeat f_equal.
           exact (f_equal snd H_sload_result).
Qed.
