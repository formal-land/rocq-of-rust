Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import bytes.simulate.bytes.
Require Import core.links.array.
Require Import core.links.result.
Require Import core.simulate.option.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_context_interface.simulate.journaled_state.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.host.extcodesize.
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
Require Import ruint.links.lib.
Require Import ruint.simulate.from.

Definition extcodesize
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  popn_top_macro interpreter 0 (fun interpreter => (interpreter, host)) (fun _ top interpreter =>
  let address :=
    Impl_IntoAddress_for_U256.into_address
      (top.(RefStub.projection) interpreter.(Interpreter.stack)) in
  let spec_id :=
    IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  let set_size account interpreter host :=
    let size : aliases.U256.t :=
      Impl_Uint.from
        (Impl_Bytes.len (account_info_load_original_bytes account).(Bytes.value)) in
    let stack := top.(RefStub.injection) interpreter.(Interpreter.stack) size in
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
        set_size account interpreter host)
      else
        set_size account interpreter host
    | Result.Err LoadError.ColdLoadSkipped =>
      (halt_oog interpreter, host)
    | Result.Err LoadError.DBError =>
      (halt_fatal interpreter, host)
    end)
  else
    gas_macro interpreter
      (if Impl_SpecId.is_enabled_in spec_id SpecId.TANGERINE then
        700
      else
        20)
      (fun interpreter => (interpreter, host))
      (fun interpreter =>
    let '(account_result, host) :=
      IHost.(Host.load_account_info_skip_cold_load) host address true false in
    match account_result with
    | Result.Ok account => set_size account interpreter host
    | Result.Err _ => (halt_fatal interpreter, host)
    end)).

Ltac load_account_info_code_len_eq host_eq H_load :=
  lazymatch type of H_load with
  | @Host.load_account_info_skip_cold_load _ _ _ _ ?IHost
      ?self ?address true ?skip_cold_load =
      (Result.Ok ?account, ?self_after) =>
      lazymatch goal with
      | |- Run.t _
          (SimulateM.Call
            (?interpreter :: ?self_after :: ?stack)%stack
            (Impl_Deref_for_AccountInfoLoad.run_deref ?ref_account).(Run.run_f)
            _) =>
          let H_account_read := fresh "H_account_read" in
          assert (H_account_read :
            CanRead.t
              (interpreter :: self_after :: stack)%stack
              account
              ref_account) by (
            first [
              apply CanRead.Immediate
            |
              cbn;
              unshelve eapply CanRead.Mutable;
              [repeat constructor | reflexivity]
            ]
          );
          let ref_account_info := fresh "ref_account_info" in
          let ref_bytecode := fresh "ref_bytecode" in
          let H_deref := fresh "H_deref" in
          let H_as_ref := fresh "H_as_ref" in
          let H_bytecode_len := fresh "H_bytecode_len" in
          destruct
            (Host.Eq.load_account_info_skip_cold_load_code_len
              (t := host_eq)
              interpreter self self_after address skip_cold_load
              account stack ref_account H_load H_account_read)
            as (ref_account_info & ref_bytecode & H_deref & H_as_ref & H_bytecode_len);
          eapply Run.Call; [exact H_deref |];
          cbn;
          eapply Run.Call; [exact H_as_ref |];
          cbn;
          eapply Run.Call; [
            eapply Impl_Option.unwrap_eq;
            reflexivity
          |];
          cbn;
          eapply Run.Call; [exact H_bytecode_len |];
          cbn
      end
  end.

Lemma extcodesize_eq
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
  let result := extcodesize interpreter host in
  {{
    SimulateM.eval_f
      (run_extcodesize run_InterpreterTypes_for_WIRE run_Host_for_H context)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
  with_strategy transparent [run_extcodesize] unfold extcodesize, run_extcodesize; cbn.
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
    destruct
      (IHost.(Host.load_account_info_skip_cold_load) host
        (Impl_IntoAddress_for_U256.into_address (t0.(RefStub.projection) s))
        true
        (i[Impl_Gas.remaining s0] <? (2600 - 100) mod 2 ^ 64))
      as [[account|load_error] host_after] eqn:H_account_load; cbn.
    +
      destruct account as [account_info account_is_cold account_is_empty]; cbn in *.
      destruct account_is_cold; cbn.
      * setoid_rewrite H_account_load.
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
           eapply Run.Call. {
             apply Run.Pure.
           }
           cbn.
           apply Run.LetUnfold.
           cbn.
           setoid_rewrite H_account_load.
           cbn.
           load_account_info_code_len_eq HostEq H_account_load.
           s. {
             s_apply Impl_Uint.from_eq.
           }
           s.
        -- eapply Run.Call. {
             apply Run.Pure.
           }
           cbn.
           s. {
             eapply halt_oog_eq;
             exact InterpreterTypesEq.
           }
           cbn.
           setoid_rewrite H_account_load.
           cbn.
           apply Run.Pure.
      * setoid_rewrite H_account_load.
        cbn.
        apply Run.LetUnfold.
        cbn.
        eapply Run.Call. {
          apply Run.Pure.
        }
        cbn.
        apply Run.LetUnfold.
        cbn.
        setoid_rewrite H_account_load.
        cbn.
        load_account_info_code_len_eq HostEq H_account_load.
        s. {
          s_apply Impl_Uint.from_eq.
        }
        s.
    +
      destruct load_error; cbn.
      * setoid_rewrite H_account_load.
        cbn [LoadError.IsLink].
        s.
        setoid_rewrite H_account_load.
        cbn [LoadError.IsLink].
        s.
        with_strategy transparent [φ] cbn.
        setoid_rewrite H_account_load.
        cbn.
        s. {
          eapply halt_fatal_eq;
          exact InterpreterTypesEq.
        }
        cbn.
        s.
        exact (f_equal snd H_account_load).
      * setoid_rewrite H_account_load.
        cbn [LoadError.IsLink].
        s.
        setoid_rewrite H_account_load.
        cbn [LoadError.IsLink].
        s. {
          eapply halt_oog_eq;
          exact InterpreterTypesEq.
        }
        cbn.
        s.
        exact (f_equal snd H_account_load).
  }
  { s. {
      apply Impl_SpecId.is_enabled_in_eq.
    }
    destruct Impl_SpecId.is_enabled_in; cbn.
    - gas_macro_eq idtac.
      s. {
        apply HostEq.
      }
      destruct
        (IHost.(Host.load_account_info_skip_cold_load) host
          (Impl_IntoAddress_for_U256.into_address (t0.(RefStub.projection) s))
          true false)
        as [[account|load_error] host_after] eqn:H_account_load; cbn.
      + cbn.
        apply Run.LetUnfold.
        cbn.
        load_account_info_code_len_eq HostEq H_account_load.
        s. {
          s_apply Impl_Uint.from_eq.
        }
        s.
      + cbn.
        s. {
          eapply halt_fatal_eq;
          exact InterpreterTypesEq.
        }
        cbn.
        apply Run.PureEq.
        cbn.
        repeat f_equal.
    - gas_macro_eq idtac.
      s. {
        apply HostEq.
      }
      destruct
        (IHost.(Host.load_account_info_skip_cold_load) host
          (Impl_IntoAddress_for_U256.into_address (t0.(RefStub.projection) s))
          true false)
        as [[account|load_error] host_after] eqn:H_account_load; cbn.
      + cbn.
        apply Run.LetUnfold.
        cbn.
        load_account_info_code_len_eq HostEq H_account_load.
        s. {
          s_apply Impl_Uint.from_eq.
        }
        s.
      + cbn.
        s. {
          eapply halt_fatal_eq;
          exact InterpreterTypesEq.
        }
        cbn.
        apply Run.PureEq.
        cbn.
        repeat f_equal.
  }
Qed.
