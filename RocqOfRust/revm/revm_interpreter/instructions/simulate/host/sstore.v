Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.links.result.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.host.sstore.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.

Definition sstore
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  require_non_staticcall_macro interpreter
    (fun interpreter => (interpreter, host)) (fun interpreter =>

  popn_macro interpreter 2 (fun interpreter => (interpreter, host)) (fun arr interpreter =>
  let '⟬ index; value ⟭ := arr.(array.value) in
  let target :=
    IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.target_address)
      interpreter.(Interpreter.input) in
  let spec_id :=
    IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  if (Bool.eqb (Impl_SpecId.is_enabled_in spec_id SpecId.ISTANBUL) true)
      && (Bool.eqb
        (i[Impl_Gas.remaining interpreter.(Interpreter.gas)] <=? i[constants.CALL_STIPEND])
        true) then
    (halt interpreter instruction_result.InstructionResult.ReentrancySentryOOG, host)
  else
  gas_macro interpreter
    (calc.static_sstore_cost spec_id)
    (fun interpreter => (interpreter, host)) (fun interpreter =>
  if Impl_SpecId.is_enabled_in spec_id SpecId.BERLIN then
    let skip_cold :=
      i[Impl_Gas.remaining interpreter.(Interpreter.gas)] <?
      COLD_SLOAD_COST_ADDITIONAL.(Integer.value) in
    let '(result, host) :=
      IHost.(Host.sstore_skip_cold_load) host target index value skip_cold in
    match result with
    | Result.Ok state_load =>
        gas_macro interpreter
          (calc.dyn_sstore_cost
            spec_id state_load.(StateLoad.data) state_load.(StateLoad.is_cold))
          (fun interpreter => (interpreter, host)) (fun interpreter =>

        let vals_ref : '& SStoreResult.t :=
          Ref.immediate Pointer.Kind.Ref state_load.(StateLoad.data) in
        let refund := calc.sstore_refund spec_id vals_ref in
        let gas := Impl_Gas.record_refund interpreter.(Interpreter.gas) refund in
        (interpreter <| Interpreter.gas := gas |>, host))
    | Result.Err LoadError.ColdLoadSkipped =>
        (halt_oog interpreter, host)
    | Result.Err LoadError.DBError =>
        (halt_fatal interpreter, host)
    end
  else
    let '(result, host) := IHost.(Host.sstore) host target index value in
    match result with
    | Some state_load =>
        gas_macro interpreter
          (calc.dyn_sstore_cost
            spec_id state_load.(StateLoad.data) state_load.(StateLoad.is_cold))
          (fun interpreter => (interpreter, host)) (fun interpreter =>

        let vals_ref : '& SStoreResult.t :=
          Ref.immediate Pointer.Kind.Ref state_load.(StateLoad.data) in
        let refund := calc.sstore_refund spec_id vals_ref in
        let gas := Impl_Gas.record_refund interpreter.(Interpreter.gas) refund in
        (interpreter <| Interpreter.gas := gas |>, host))
    | None =>
        (halt_fatal interpreter, host)
    end))).

Ltac normalize_dynamic_sstore_cost H_dynamic_gas :=
  unfold
    calc.dyn_sstore_cost,
    calc.sstore_cost,
    calc.sstore_cost_value,
    calc.istanbul_sstore_cost_value,
    calc.frontier_sstore_cost_value
    in H_dynamic_gas |- *;
  cbn in H_dynamic_gas |- *.

Ltac destruct_dynamic_sstore_cost :=
  match goal with
  | |- context[
      Impl_Gas.record_cost ?gas
        (calc.dyn_sstore_cost ?spec_id ?values ?is_cold)] =>
      destruct
        (Impl_Gas.record_cost gas
          (calc.dyn_sstore_cost spec_id values is_cold))
        as [gas_after_dynamic|] eqn:H_dynamic_gas
  end.

Lemma sstore_eq
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
  let result := sstore interpreter host in
  {{
    SimulateM.eval_f
      (run_sstore run_InterpreterTypes_for_WIRE run_Host_for_H context)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
  intros.
  subst result.
  with_strategy transparent [run_sstore] unfold sstore, run_sstore; cbn.
  require_non_staticcall_macro_eq InterpreterTypesEq.
  popn_macro_eq InterpreterTypesEq.
  match goal with
  | arr : array.t aliases.U256.t _ |- _ =>
    destruct arr as [[index [value []]]]
  end.
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply Impl_SpecId.is_enabled_in_eq.
  }
  destruct
    (Bool.eqb
      (Impl_SpecId.is_enabled_in
      (IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
        .(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag))
      SpecId.ISTANBUL)
      true) eqn:H_istanbul; cbn.
  - eapply Run.Call
      with
        (output_inter := true)
        (stack_inter :=
          [interpreter<|Interpreter.stack := s|>; host; tt;
           IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input)
             .(InputTraits.target_address) interpreter.(Interpreter.input);
           IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
             .(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag)]%stack).
    {
      apply Run.PureEq.
      cbn.
      repeat f_equal.
      exact H_istanbul.
    }
    cbn.
    eapply Run.Call. {
      apply Impl_Gas.remaining_interpreter_eq.
    }
    cbn.
    eapply Run.Call. {
      apply CALL_STIPEND_eq.
    }
    cbn.
    eapply Run.Call. {
      apply Run.Pure.
    }
    cbn.
    destruct
      (Bool.eqb
        (i[Impl_Gas.remaining interpreter.(Interpreter.gas)] <=? i[constants.CALL_STIPEND])
        true) eqn:H_stipend; cbn.
    + eapply Run.Call
        with
          (output_inter := true)
          (stack_inter :=
            [interpreter<|Interpreter.stack := s|>; host; tt;
             IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input)
               .(InputTraits.target_address) interpreter.(Interpreter.input);
             IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
               .(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag)]%stack).
      {
        apply Run.PureEq.
        cbn.
        repeat f_equal.
        exact H_stipend.
      }
      cbn.
      s. {
        eapply halt_eq;
        exact InterpreterTypesEq.
      }
      cbn.
      unfold sstore.
      cbn.
      replace
        (Bool.eqb
          (Impl_SpecId.is_enabled_in
          (IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
            .(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag))
          SpecId.ISTANBUL)
        true)
        with true by (symmetry; exact H_istanbul).
      cbn.
      replace
        (Bool.eqb
          (i[Impl_Gas.remaining interpreter.(Interpreter.gas)] <=? i[constants.CALL_STIPEND])
          true)
        with true by (symmetry; exact H_stipend).
      cbn.
      apply Run.PureEq.
      cbn.
      setoid_rewrite H_istanbul.
      setoid_rewrite H_stipend.
      cbn.
      reflexivity.
    + eapply Run.Call
        with
          (output_inter := false)
          (stack_inter :=
            [interpreter<|Interpreter.stack := s|>; host; tt;
             IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input)
               .(InputTraits.target_address) interpreter.(Interpreter.input);
             IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
               .(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag)]%stack).
      {
        apply Run.PureEq.
        cbn.
        repeat f_equal.
        exact H_stipend.
      }
      cbn.
      s. {
        apply InterpreterTypesEq.
      }
      eapply Run.Call. {
        apply calc.static_sstore_cost_eq.
      }
      cbn.
      s. {
        apply Impl_Gas.record_cost_interpreter_eq.
      }
      destruct
        (Impl_Gas.record_cost
          interpreter.(Interpreter.gas)
          (calc.static_sstore_cost
            (IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
              .(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag)))
        ) as [gas_after_static|] eqn:H_static_gas; cbn.
      * eapply Run.Call
          with
            (output_inter := false)
            (stack_inter :=
              [interpreter<|Interpreter.stack := s|><|Interpreter.gas := gas_after_static|>;
               host; tt;
               IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input)
                 .(InputTraits.target_address) interpreter.(Interpreter.input);
               IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
                 .(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag);
               tt]%stack).
        {
          apply Run.PureEq.
          cbn.
          setoid_rewrite H_static_gas.
          cbn.
          reflexivity.
        }
        cbn.
        eapply Run.Call
          with
            (output_inter := false)
            (stack_inter :=
              [interpreter<|Interpreter.stack := s|><|Interpreter.gas := gas_after_static|>;
               host; tt;
               IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input)
                 .(InputTraits.target_address) interpreter.(Interpreter.input);
               IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
                 .(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag);
               tt]%stack).
        {
          apply Run.Pure.
        }
        cbn.
        apply Run.LetUnfold.
        cbn.
        get_can_access.
        cbn.
        eapply Run.Call. {
          apply Impl_SpecId.is_enabled_in_eq.
        }
        cbn.
        destruct
          (Impl_SpecId.is_enabled_in
            (IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
              .(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag))
            SpecId.BERLIN) eqn:H_berlin; cbn.
        -- eapply Run.Call
             with
               (output_inter := true)
               (stack_inter :=
                 [interpreter<|Interpreter.stack := s|><|Interpreter.gas := gas_after_static|>;
                  host; tt;
                  IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input)
                    .(InputTraits.target_address) interpreter.(Interpreter.input);
                  IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
                    .(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag);
                  tt; tt]%stack).
           {
             apply Run.PureEq.
             cbn.
             repeat f_equal.
	           }
	           cbn.
	           apply Run.LetUnfold.
	           cbn.
	           eapply Run.Call. {
	             apply Impl_Gas.remaining_interpreter_eq.
	           }
	           cbn.
	           eapply Run.Call. {
	             apply COLD_SLOAD_COST_ADDITIONAL_eq.
	           }
	           cbn.
		           eapply Run.Call. {
		             apply Run.Pure.
		           }
		           cbn.
			           apply Run.LetUnfold.
			           cbn.
			           get_can_access.
			           cbn.
			           get_can_access.
			           cbn.
			           eapply Run.Call. {
			             apply HostEq.
			           }
		           destruct
		             (IHost.(Host.sstore_skip_cold_load) host
		               (IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input)
		                 .(InputTraits.target_address) interpreter.(Interpreter.input))
		               index value
		               (i[Impl_Gas.remaining gas_after_static] <? (2100 - 100) mod 2 ^ 64))
		             as [[state_load|load_error] host_after] eqn:H_sstore_result;
		             cbn.
	           ++ get_can_access.
	              cbn.
	              setoid_rewrite H_sstore_result.
	              cbn.
	              s. {
	                apply InterpreterTypesEq.
	              }
	              get_can_access.
	              cbn.
	              eapply Run.Call. {
	                eapply calc.dyn_sstore_cost_eq
	                  with (vals := state_load.(StateLoad.data)).
	                repeat unshelve econstructor.
	              }
	              cbn.
	              s. {
	                apply Impl_Gas.record_cost_interpreter_eq.
	              }
	              destruct_dynamic_sstore_cost;
	              cbn.
	              ** eapply Run.Call. {
	                   apply Run.Pure.
	                 }
	                 cbn.
	                 eapply Run.Call. {
	                   apply Run.Pure.
	                 }
	                 cbn.
	                 apply Run.LetUnfold.
	                 cbn.
	                 s. {
	                   apply InterpreterTypesEq.
	                 }
	                 eapply Run.Call. {
	                   apply calc.sstore_refund_eq.
	                 }
		                 cbn.
		                 s. {
		                   apply Impl_Gas.record_refund_interpreter_eq.
		                 }
		                 cbn.
		                 apply Run.PureEq.
	                 cbn.
	                 setoid_rewrite H_istanbul.
	                 cbn.
	                 setoid_rewrite H_stipend.
	                 cbn.
	                 unfold gas_macro.
	                 cbn.
	                 setoid_rewrite H_static_gas.
	                 cbn.
	                 symmetry in H_berlin.
	                 destruct H_berlin.
	                 cbn.
	                 setoid_rewrite H_sstore_result.
	                 cbn.
	                 unfold gas_macro.
	                 cbn.
	                 normalize_dynamic_sstore_cost H_dynamic_gas.
	                 setoid_rewrite H_dynamic_gas.
	                 cbn.
	                 unfold calc.sstore_refund.
	                 cbn.
	                 reflexivity.
	              ** s. {
	                   eapply halt_oog_eq;
	                   exact InterpreterTypesEq.
	                 }
	                 cbn.
	                 apply Run.PureEq.
	                 cbn.
	                 setoid_rewrite H_istanbul.
	                 cbn.
	                 setoid_rewrite H_stipend.
	                 cbn.
	                 unfold gas_macro.
	                 cbn.
	                 setoid_rewrite H_static_gas.
	                 cbn.
	                 setoid_rewrite H_sstore_result.
	                 cbn.
	                 unfold gas_macro.
	                 cbn.
	                 normalize_dynamic_sstore_cost H_dynamic_gas.
	                 setoid_rewrite H_dynamic_gas.
	                 cbn.
	                 symmetry in H_berlin.
	                 destruct H_berlin.
	                 cbn.
	                 reflexivity.
		           ++ destruct load_error; cbn.
		              ** get_can_access.
		                 cbn.
		                 setoid_rewrite H_sstore_result.
		                 cbn.
		                 get_can_access.
		                 cbn.
		                 setoid_rewrite H_sstore_result.
		                 cbn.
		                 setoid_rewrite H_sstore_result.
		                 cbn.
			                 s. {
			                   eapply halt_fatal_eq;
			                   exact InterpreterTypesEq.
			                 }
			                 cbn.
			                 apply Run.PureEq.
			                 cbn.
			                 setoid_rewrite H_istanbul.
			                 cbn.
			                 setoid_rewrite H_stipend.
			                 cbn.
			                 unfold gas_macro.
			                 cbn.
			                 setoid_rewrite H_static_gas.
			                 cbn.
			                 setoid_rewrite H_sstore_result.
			                 cbn.
			                 symmetry in H_berlin.
			                 destruct H_berlin.
			                 cbn.
			                 reflexivity.
		              ** get_can_access.
		                 cbn.
		                 setoid_rewrite H_sstore_result.
		                 cbn.
		                 get_can_access.
		                 cbn.
		                 setoid_rewrite H_sstore_result.
		                 cbn.
		                 s. {
		                   eapply halt_oog_eq;
		                   exact InterpreterTypesEq.
		                 }
		                 cbn.
			                 apply Run.PureEq.
			                 cbn.
			                 setoid_rewrite H_istanbul.
			                 cbn.
			                 setoid_rewrite H_stipend.
			                 cbn.
			                 unfold gas_macro.
			                 cbn.
			                 setoid_rewrite H_static_gas.
			                 cbn.
			                 setoid_rewrite H_sstore_result.
			                 cbn.
			                 symmetry in H_berlin.
			                 destruct H_berlin.
			                 cbn.
			                 reflexivity.
	        -- eapply Run.Call
	             with
	               (output_inter := false)
	               (stack_inter :=
	                 [interpreter<|Interpreter.stack := s|><|Interpreter.gas := gas_after_static|>;
	                  host; tt;
	                  IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input)
	                    .(InputTraits.target_address) interpreter.(Interpreter.input);
	                  IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
	                    .(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag);
	                  tt; tt]%stack).
		           {
		             apply Run.PureEq.
		             cbn.
		             repeat f_equal.
		           }
		           cbn.
		           get_can_access.
		           cbn.
		           eapply Run.Call. {
		             apply HostEq.
		           }
		           destruct
			             (IHost.(Host.sstore) host
			               (IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input)
			                 .(InputTraits.target_address) interpreter.(Interpreter.input))
			               index value)
			             as [[state_load|] host_after] eqn:H_sstore_result;
			             cbn.
	           ++ s. {
	                apply InterpreterTypesEq.
	              }
	              get_can_access.
	              cbn.
	              eapply Run.Call. {
	                eapply calc.dyn_sstore_cost_eq
	                  with (vals := state_load.(StateLoad.data)).
	                repeat unshelve econstructor.
	              }
	              cbn.
	              s. {
	                apply Impl_Gas.record_cost_interpreter_eq.
	              }
	              destruct_dynamic_sstore_cost;
	              cbn.
	              ** eapply Run.Call. {
	                   apply Run.Pure.
	                 }
	                 cbn.
	                 eapply Run.Call. {
	                   apply Run.Pure.
	                 }
	                 cbn.
	                 apply Run.LetUnfold.
	                 cbn.
	                 s. {
	                   apply InterpreterTypesEq.
	                 }
	                 eapply Run.Call. {
	                   apply calc.sstore_refund_eq.
	                 }
	                 cbn.
	                 s. {
	                   apply Impl_Gas.record_refund_interpreter_eq.
	                 }
	                 cbn.
	                 apply Run.PureEq.
	                 cbn.
	                 setoid_rewrite H_istanbul.
	                 cbn.
	                 setoid_rewrite H_stipend.
	                 cbn.
	                 unfold gas_macro.
	                 cbn.
	                 setoid_rewrite H_static_gas.
	                 cbn.
	                 symmetry in H_berlin.
	                 destruct H_berlin.
	                 cbn.
	                 setoid_rewrite H_sstore_result.
	                 cbn.
	                 unfold gas_macro.
	                 cbn.
	                 normalize_dynamic_sstore_cost H_dynamic_gas.
	                 setoid_rewrite H_dynamic_gas.
	                 cbn.
	                 unfold calc.sstore_refund.
	                 cbn.
	                 reflexivity.
	              ** s. {
	                   eapply halt_oog_eq;
	                   exact InterpreterTypesEq.
	                 }
	                 cbn.
	                 apply Run.PureEq.
	                 cbn.
	                 setoid_rewrite H_istanbul.
	                 cbn.
	                 setoid_rewrite H_stipend.
	                 cbn.
	                 unfold gas_macro.
	                 cbn.
	                 setoid_rewrite H_static_gas.
	                 cbn.
	                 symmetry in H_berlin.
	                 destruct H_berlin.
	                 cbn.
	                 setoid_rewrite H_sstore_result.
	                 cbn.
	                 unfold gas_macro.
	                 cbn.
	                 normalize_dynamic_sstore_cost H_dynamic_gas.
	                 setoid_rewrite H_dynamic_gas.
	                 cbn.
	                 reflexivity.
		           ++ s. {
	                eapply halt_fatal_eq;
	                exact InterpreterTypesEq.
	              }
	              cbn.
	              apply Run.PureEq.
	              cbn.
	              setoid_rewrite H_istanbul.
	              cbn.
	              setoid_rewrite H_stipend.
	              cbn.
	              unfold gas_macro.
	              cbn.
	              setoid_rewrite H_static_gas.
	              cbn.
	              symmetry in H_berlin.
	              destruct H_berlin.
		              cbn.
		              setoid_rewrite H_sstore_result.
		              cbn.
		              reflexivity.
      * eapply Run.Call. {
          apply Run.Pure.
        }
        cbn.
        eapply Run.Call. {
          apply Run.Pure.
        }
        cbn.
        setoid_rewrite H_static_gas.
        cbn.
        apply Run.LetUnfold.
        cbn.
        eapply Run.Call. {
          eapply halt_oog_eq;
          exact InterpreterTypesEq.
        }
        cbn.
        unfold sstore.
        cbn.
        setoid_rewrite H_istanbul.
        setoid_rewrite H_stipend.
        cbn.
        unfold gas_macro.
        cbn.
        apply Run.PureEq.
        cbn.
        setoid_rewrite H_static_gas.
        cbn.
        reflexivity.
  - eapply Run.Call
      with
        (output_inter := false)
        (stack_inter :=
          [interpreter<|Interpreter.stack := s|>; host; tt;
           IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input)
             .(InputTraits.target_address) interpreter.(Interpreter.input);
           IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
             .(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag)]%stack).
    {
      apply Run.PureEq.
      cbn.
      repeat f_equal.
      exact H_istanbul.
	    }
	    cbn.
	    s. {
	      apply InterpreterTypesEq.
	    }
	    eapply Run.Call. {
	      apply calc.static_sstore_cost_eq.
	    }
	    cbn.
	    s. {
	      apply Impl_Gas.record_cost_interpreter_eq.
	    }
	    destruct
	      (Impl_Gas.record_cost
	        interpreter.(Interpreter.gas)
	        (calc.static_sstore_cost
	          (IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
	            .(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag)))
	      ) as [gas_after_static|] eqn:H_static_gas; cbn.
	    + eapply Run.Call
	        with
	          (output_inter := false)
	          (stack_inter :=
	            [interpreter<|Interpreter.stack := s|><|Interpreter.gas := gas_after_static|>;
	             host; tt;
	             IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input)
	               .(InputTraits.target_address) interpreter.(Interpreter.input);
	             IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
	               .(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag);
	             tt]%stack).
	      {
	        apply Run.PureEq.
	        cbn.
	        setoid_rewrite H_static_gas.
	        cbn.
	        reflexivity.
	      }
	      cbn.
	      eapply Run.Call
	        with
	          (output_inter := false)
	          (stack_inter :=
	            [interpreter<|Interpreter.stack := s|><|Interpreter.gas := gas_after_static|>;
	             host; tt;
	             IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input)
	               .(InputTraits.target_address) interpreter.(Interpreter.input);
	             IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
	               .(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag);
	             tt]%stack).
	      {
	        apply Run.Pure.
	      }
	      cbn.
	      apply Run.LetUnfold.
	      cbn.
	      get_can_access.
	      cbn.
	      eapply Run.Call. {
	        apply Impl_SpecId.is_enabled_in_eq.
	      }
	      cbn.
	      destruct
	        (Impl_SpecId.is_enabled_in
	          (IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
	            .(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag))
	          SpecId.BERLIN) eqn:H_berlin; cbn.
	      * eapply Run.Call
	          with
	            (output_inter := true)
	            (stack_inter :=
	              [interpreter<|Interpreter.stack := s|><|Interpreter.gas := gas_after_static|>;
	               host; tt;
	               IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input)
	                 .(InputTraits.target_address) interpreter.(Interpreter.input);
	               IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
	                 .(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag);
	               tt; tt]%stack).
	        {
	          apply Run.PureEq.
	          cbn.
	          repeat f_equal.
	        }
	        cbn.
	        apply Run.LetUnfold.
	        cbn.
	        eapply Run.Call. {
	          apply Impl_Gas.remaining_interpreter_eq.
	        }
	        cbn.
	        eapply Run.Call. {
	          apply COLD_SLOAD_COST_ADDITIONAL_eq.
	        }
	        cbn.
	        eapply Run.Call. {
	          apply Run.Pure.
	        }
	        cbn.
	        apply Run.LetUnfold.
	        cbn.
	        get_can_access.
	        cbn.
	        get_can_access.
	        cbn.
	        eapply Run.Call. {
	          apply HostEq.
	        }
	        destruct
	          (IHost.(Host.sstore_skip_cold_load) host
	            (IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input)
	              .(InputTraits.target_address) interpreter.(Interpreter.input))
	            index value
	            (i[Impl_Gas.remaining gas_after_static] <? (2100 - 100) mod 2 ^ 64))
	          as [[state_load|load_error] host_after] eqn:H_sstore_result;
	          cbn.
	        -- get_can_access.
	           cbn.
	           setoid_rewrite H_sstore_result.
	           cbn.
	           s. {
	             apply InterpreterTypesEq.
	           }
	           get_can_access.
	           cbn.
	           eapply Run.Call. {
	             eapply calc.dyn_sstore_cost_eq
	               with (vals := state_load.(StateLoad.data)).
	             repeat unshelve econstructor.
	           }
	           cbn.
	           s. {
	             apply Impl_Gas.record_cost_interpreter_eq.
	           }
	           destruct_dynamic_sstore_cost;
	           cbn.
	           ++ eapply Run.Call. {
	                apply Run.Pure.
	              }
	              cbn.
	              eapply Run.Call. {
	                apply Run.Pure.
	              }
	              cbn.
	              apply Run.LetUnfold.
	              cbn.
	              s. {
	                apply InterpreterTypesEq.
	              }
	              eapply Run.Call. {
	                apply calc.sstore_refund_eq.
	              }
	              cbn.
	              s. {
	                apply Impl_Gas.record_refund_interpreter_eq.
	              }
	              cbn.
	              apply Run.PureEq.
	              cbn.
	              setoid_rewrite H_istanbul.
	              cbn.
	              unfold gas_macro.
	              cbn.
	              setoid_rewrite H_static_gas.
	              cbn.
	              symmetry in H_berlin.
	              destruct H_berlin.
	              cbn.
	              setoid_rewrite H_sstore_result.
	              cbn.
	              unfold gas_macro.
	              cbn.
	              normalize_dynamic_sstore_cost H_dynamic_gas.
	              setoid_rewrite H_dynamic_gas.
	              cbn.
	              unfold calc.sstore_refund.
	              cbn.
	              reflexivity.
	           ++ s. {
	                eapply halt_oog_eq;
	                exact InterpreterTypesEq.
	              }
	              cbn.
	              apply Run.PureEq.
	              cbn.
	              setoid_rewrite H_istanbul.
	              cbn.
	              unfold gas_macro.
	              cbn.
	              setoid_rewrite H_static_gas.
	              cbn.
	              symmetry in H_berlin.
	              destruct H_berlin.
	              cbn.
	              setoid_rewrite H_sstore_result.
	              cbn.
	              unfold gas_macro.
	              cbn.
	              normalize_dynamic_sstore_cost H_dynamic_gas.
	              setoid_rewrite H_dynamic_gas.
	              cbn.
	              reflexivity.
	        -- destruct load_error; cbn.
	           ++ get_can_access.
	              cbn.
	              setoid_rewrite H_sstore_result.
	              cbn.
	              get_can_access.
	              cbn.
	              setoid_rewrite H_sstore_result.
	              cbn.
	              setoid_rewrite H_sstore_result.
	              cbn.
	              s. {
	                eapply halt_fatal_eq;
	                exact InterpreterTypesEq.
	              }
	              cbn.
	              apply Run.PureEq.
	              cbn.
	              setoid_rewrite H_istanbul.
	              cbn.
	              unfold gas_macro.
	              cbn.
	              setoid_rewrite H_static_gas.
	              cbn.
	              setoid_rewrite H_sstore_result.
	              cbn.
	              symmetry in H_berlin.
	              destruct H_berlin.
	              cbn.
	              reflexivity.
	           ++ get_can_access.
	              cbn.
	              setoid_rewrite H_sstore_result.
	              cbn.
	              get_can_access.
	              cbn.
	              setoid_rewrite H_sstore_result.
	              cbn.
	              s. {
	                eapply halt_oog_eq;
	                exact InterpreterTypesEq.
	              }
	              cbn.
	              apply Run.PureEq.
	              cbn.
	              setoid_rewrite H_istanbul.
	              cbn.
	              unfold gas_macro.
	              cbn.
	              setoid_rewrite H_static_gas.
	              cbn.
	              setoid_rewrite H_sstore_result.
	              cbn.
	              symmetry in H_berlin.
	              destruct H_berlin.
	              cbn.
	              reflexivity.
	      * eapply Run.Call
	          with
	            (output_inter := false)
	            (stack_inter :=
	              [interpreter<|Interpreter.stack := s|><|Interpreter.gas := gas_after_static|>;
	               host; tt;
	               IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input)
	                 .(InputTraits.target_address) interpreter.(Interpreter.input);
	               IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
	                 .(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag);
	               tt; tt]%stack).
	        {
	          apply Run.PureEq.
	          cbn.
	          repeat f_equal.
	        }
	        cbn.
	        get_can_access.
	        cbn.
	        eapply Run.Call. {
	          apply HostEq.
	        }
	        destruct
	          (IHost.(Host.sstore) host
	            (IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input)
	              .(InputTraits.target_address) interpreter.(Interpreter.input))
	            index value)
	          as [[state_load|] host_after] eqn:H_sstore_result;
	          cbn.
	        -- s. {
	             apply InterpreterTypesEq.
	           }
	           get_can_access.
	           cbn.
	           eapply Run.Call. {
	             eapply calc.dyn_sstore_cost_eq
	               with (vals := state_load.(StateLoad.data)).
	             repeat unshelve econstructor.
	           }
	           cbn.
	           s. {
	             apply Impl_Gas.record_cost_interpreter_eq.
	           }
	           destruct_dynamic_sstore_cost;
	           cbn.
	           ++ eapply Run.Call. {
	                apply Run.Pure.
	              }
	              cbn.
	              eapply Run.Call. {
	                apply Run.Pure.
	              }
	              cbn.
	              apply Run.LetUnfold.
	              cbn.
	              s. {
	                apply InterpreterTypesEq.
	              }
	              eapply Run.Call. {
	                apply calc.sstore_refund_eq.
	              }
	              cbn.
	              s. {
	                apply Impl_Gas.record_refund_interpreter_eq.
	              }
	              cbn.
	              apply Run.PureEq.
	              cbn.
	              setoid_rewrite H_istanbul.
	              cbn.
	              unfold gas_macro.
	              cbn.
	              setoid_rewrite H_static_gas.
	              cbn.
	              symmetry in H_berlin.
	              destruct H_berlin.
	              cbn.
	              setoid_rewrite H_sstore_result.
	              cbn.
	              unfold gas_macro.
	              cbn.
	              normalize_dynamic_sstore_cost H_dynamic_gas.
	              setoid_rewrite H_dynamic_gas.
	              cbn.
	              unfold calc.sstore_refund.
	              cbn.
	              reflexivity.
	           ++ s. {
	                eapply halt_oog_eq;
	                exact InterpreterTypesEq.
	              }
	              cbn.
	              apply Run.PureEq.
	              cbn.
	              setoid_rewrite H_istanbul.
	              cbn.
	              unfold gas_macro.
	              cbn.
	              setoid_rewrite H_static_gas.
	              cbn.
	              symmetry in H_berlin.
	              destruct H_berlin.
	              cbn.
	              setoid_rewrite H_sstore_result.
	              cbn.
	              unfold gas_macro.
	              cbn.
	              normalize_dynamic_sstore_cost H_dynamic_gas.
	              setoid_rewrite H_dynamic_gas.
	              cbn.
	              reflexivity.
	        -- s. {
	             eapply halt_fatal_eq;
	             exact InterpreterTypesEq.
	           }
	           cbn.
	           apply Run.PureEq.
	           cbn.
	           setoid_rewrite H_istanbul.
	           cbn.
	           unfold gas_macro.
	           cbn.
	           setoid_rewrite H_static_gas.
	           cbn.
	           symmetry in H_berlin.
	           destruct H_berlin.
	           cbn.
	           setoid_rewrite H_sstore_result.
	           cbn.
	           reflexivity.
	    + eapply Run.Call. {
	        apply Run.Pure.
	      }
	      cbn.
	      eapply Run.Call. {
	        apply Run.Pure.
	      }
	      cbn.
	      setoid_rewrite H_static_gas.
	      cbn.
	      apply Run.LetUnfold.
	      cbn.
	      eapply Run.Call. {
	        eapply halt_oog_eq;
	        exact InterpreterTypesEq.
	      }
	      cbn.
	      unfold sstore.
	      cbn.
	      setoid_rewrite H_istanbul.
	      cbn.
	      unfold gas_macro.
	      cbn.
	      apply Run.PureEq.
	      cbn.
	      setoid_rewrite H_static_gas.
	      cbn.
	      reflexivity.
Qed.
