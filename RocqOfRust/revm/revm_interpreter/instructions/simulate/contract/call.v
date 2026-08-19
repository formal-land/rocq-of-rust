Require Import simulate.RocqOfRust.
Require Import alloc.simulate.boxed.
Require Import alloy_primitives.bits.simulate.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.num.simulate.mod.
Require Import core.simulate.result.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.contract.simulate.call_helpers.
Require Import revm.revm_interpreter.instructions.links.contract.call.
Require Import revm.revm_interpreter.instructions.links.utility.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.instructions.simulate.utility.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import ruint.simulate.cmp.
Require Import ruint.simulate.from.
Require Import ruint.simulate.lib.

Definition call
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  popn_macro interpreter 3
    (fun interpreter => (interpreter, host)) (fun arr interpreter =>
  let '⟬ local_gas_limit; to; value ⟭ := arr.(array.value) in
  let to := Impl_IntoAddress_for_U256.into_address to in

  let local_gas_limit :=
    Impl_Result_T_E.unwrap_or
      (TryFrom_Uint_for_u64.try_from local_gas_limit)
      Impl_u64.MAX in

  let has_transfer := negb (Impl_Uint.is_zero value) in
  let is_static :=
    IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.is_static)
      interpreter.(Interpreter.runtime_flag) in

  if is_static && has_transfer then
    (halt interpreter
      instruction_result.InstructionResult.CallNotAllowedInsideStatic, host)
  else

  match call_helpers.get_memory_input_and_out_ranges interpreter with
  | (None, interpreter) => (interpreter, host)
  | (Some (input, return_memory_offset), interpreter) =>

  match call_helpers.load_acc_and_calc_gas
      interpreter host to has_transfer true local_gas_limit with
  | (None, interpreter, host) => (interpreter, host)
  | (Some load, interpreter, host) =>

  let bytecode :=
    IInterpreterTypes
        .(InterpreterTypes.LoopControl_for_Bytecode)
        .(LoopControl.set_action)
      interpreter.(Interpreter.bytecode)
      (interpreter_action.InterpreterAction.NewFrame
        (interpreter_action.FrameInput.Call
          (Impl_Box.new
            {|
              call_inputs.CallInputs.bytecode_address := to;
              call_inputs.CallInputs.caller :=
                IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.target_address) interpreter.(Interpreter.input);
              call_inputs.CallInputs.gas_limit := load.(call_helpers.LoadAccAndCalcGasResult.gas_limit);
              call_inputs.CallInputs.input := call_inputs.CallInput.SharedBuffer input;
              call_inputs.CallInputs.is_static :=
                IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.is_static)
                  interpreter.(Interpreter.runtime_flag);
              call_inputs.CallInputs.known_bytecode :=
                Some (
                  load.(call_helpers.LoadAccAndCalcGasResult.bytecode_hash),
                  load.(call_helpers.LoadAccAndCalcGasResult.bytecode)
                );
              call_inputs.CallInputs.return_memory_offset := return_memory_offset;
              call_inputs.CallInputs.scheme := call_inputs.CallScheme.Call;
              call_inputs.CallInputs.target_address := to;
              call_inputs.CallInputs.value := call_inputs.CallValue.Transfer value
            |}
      ))) in
  let interpreter :=
    interpreter <| Interpreter.bytecode := bytecode |> in

  (interpreter, host)
  end end).

Lemma call_eq
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
    (host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  let context := {|
    instruction_context.InstructionContext.interpreter := ref_interpreter;
    instruction_context.InstructionContext.host := ref_host;
  |} in
  {{
    SimulateM.eval_f (
      run_call
        run_InterpreterTypes_for_WIRE run_Host_for_H context
      )
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      let (interpreter, host) := call interpreter host in
      [interpreter; host]%stack
    )
  }}.
Proof.
  intros.
  with_strategy transparent [run_call]
    unfold call, run_call;
    cbn.
  popn_macro_eq InterpreterTypesEq.
  match goal with
  | arr : array.t aliases.U256.t _ |- _ =>
    destruct arr as [[local_gas_limit [to [value []]]]]
  end.
  lu.
  cw Impl_IntoAddress_for_U256.into_address_eq.
  lu.
  cw TryFrom_Uint_for_u64.try_from_eq.
  cw Impl_u64.max_eq.
  cw @Impl_Result_T_E.unwrap_or_eq.
  l. {
    cw @Impl_Uint.is_zero_eq.
    s.
    reflexivity.
  }
  match goal with
  | |- context[?e1 && ?e2] =>
    set (condition1 := e1);
    set (condition2 := e2)
  end.
  eapply Run.Let with (result :=
    if condition1 then
      if condition2 then
        _
      else
        _
    else
      _
  ). {
    s. {
      apply InterpreterTypesEq.
    }
    destruct IInterpreterTypes
      .(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
      .(RuntimeFlag.is_static).
    { s.
      destruct Impl_Uint.is_zero.
      { s.
        change false with condition2.
        reflexivity.
      }
      { s. {
          eapply halt_eq;
          exact InterpreterTypesEq.
        }
        s.
        reflexivity.
      }
    }
    { s.
      reflexivity.
    }
  }
  s.
  destruct (condition1 && condition2) eqn:H_conditions.
  { replace condition1 with true by
      (destruct condition1, condition2; cbn in H_conditions; congruence).
    replace condition2 with true by
      (destruct condition1, condition2; cbn in H_conditions; congruence).
    s.
  }
  { set (if_result := if _ : bool then _ else _).
    set (common_result := (Output.Success tt, _)) in if_result.
    replace if_result with common_result. 2: {
      unfold if_result.
      destruct condition1, condition2; cbn in H_conditions; congruence.
    }
    unfold common_result, condition1, condition2.
    s. {
      s_apply @call_helpers.get_memory_input_and_out_ranges_eq.
    }
    destruct (call_helpers.get_memory_input_and_out_ranges
      (interpreter <| Interpreter.stack := s |>)) as [
        [[input return_memory_offset] |] interpreter'
      ]; cbn.
    2: p.
    destruct (call_helpers.load_acc_and_calc_gas
      interpreter'
      host
      (Impl_IntoAddress_for_U256.into_address to)
      (negb (Impl_Uint.is_zero value))
      true
      (Impl_Result_T_E.unwrap_or
        (TryFrom_Uint_for_u64.try_from local_gas_limit) Impl_u64.MAX)
    ) as [[load_result interpreter''] host'] eqn:H_load_result; cbn.
    s. {
      pose proof (call_helpers.load_acc_and_calc_gas_eq
        (IInterpreterTypes := IInterpreterTypes)
        (InterpreterTypesEq := InterpreterTypesEq)
        (IHost := IHost)
        (HostEq := HostEq)
        run_InterpreterTypes_for_WIRE
        run_Host_for_H
        interpreter'
        host
        (Impl_IntoAddress_for_U256.into_address to)
        (negb (Impl_Uint.is_zero value))
        true
        (Impl_Result_T_E.unwrap_or
          (TryFrom_Uint_for_u64.try_from local_gas_limit) Impl_u64.MAX)
        [Impl_IntoAddress_for_U256.into_address to;
         Impl_Result_T_E.unwrap_or
           (TryFrom_Uint_for_u64.try_from local_gas_limit) Impl_u64.MAX;
         negb (Impl_Uint.is_zero value);
         tt]%stack
      ) as H_load.
      rewrite H_load_result in H_load; cbn in H_load.
      with_strategy transparent [
        call_helpers.instructions.contract.call_helpers.load_acc_and_calc_gas
      ] cbn in H_load.
      unfold context, ref_interpreter, ref_host,
        Ref.immediate, Ref.cast_to in H_load |- *.
      exact H_load.
    }
    destruct load_result as [load |]; cbn.
    2: p.
    lu.
    s. {
      apply InterpreterTypesEq.
    }
    s. {
      apply InterpreterTypesEq.
    }
    s. {
      match goal with
      | |- {{ SimulateM.eval
          (evaluate (boxed.Impl_Box.run_new ?call_inputs).(Run.run_f))
          ?stack 🌲 _ }} =>
        pose proof (@Impl_Box.new_eq
          call_inputs.CallInputs.t
          call_inputs.CallInputs.IsLink
          stack
          call_inputs
        ) as H_box
      end.
      with_strategy transparent [
        boxed.boxed.Impl_alloc_boxed_Box_T_alloc_alloc_Global.new
      ] cbn in H_box.
      exact H_box.
    }
    s. {
      apply InterpreterTypesEq.
    }
    s.
  }
Qed.
