Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import bytes.simulate.bytes.
Require Import core.links.array.
Require Import core.num.simulate.mod.
Require Import core.simulate.cmp.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_context_interface.simulate.journaled_state.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.instructions.links.host.extcodecopy.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.instructions.simulate.utility.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.simulate.lib.

Definition extcodecopy
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  popn_macro interpreter 4 (fun interpreter => (interpreter, host)) (fun arr interpreter =>
  let '⟬ address; memory_offset; code_offset; len_u256 ⟭ := arr.(array.value) in
  let address := Impl_IntoAddress_for_U256.into_address address in
  let '(code_opt, host) := IHost.(Host.code) host address in
  match code_opt with
  | None =>
    let control :=
      IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.FatalExternalError in
    (interpreter <| Interpreter.control := control |>, host)
  | Some code =>

  as_usize_or_fail_ret_macro interpreter len_u256 None
    (fun interpreter => (interpreter, host)) (fun len interpreter =>
  let '(code, load) := Impl_Eip7702CodeLoad.into_components code in
  let spec_id :=
    IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  gas_or_fail_macro interpreter (calc.extcodecopy_cost spec_id len load)
    (fun interpreter => (interpreter, host)) (fun interpreter =>
  if i[len] =? 0 then
    (interpreter, host)
  else
  as_usize_or_fail_ret_macro interpreter memory_offset None
    (fun interpreter => (interpreter, host)) (fun memory_offset interpreter =>
  let code_len := Impl_Bytes.len code.(Bytes.value) in
  let code_offset := Z.min (i[as_usize_saturated_macro code_offset] mod 2^64) i[code_len] in
  resize_memory_macro interpreter memory_offset len
    (fun interpreter => (interpreter, host)) (fun interpreter =>

  let memory :=
    IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.set_data)
      interpreter.(Interpreter.memory)
      memory_offset
      code_offset
      len
      code.(Bytes.value).(bytes.Bytes.value) in
  (interpreter <| Interpreter.memory := memory |>, host)
  )))) end).

Lemma extcodecopy_eq
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
  let result := extcodecopy interpreter host in
  {{
    SimulateM.eval_f
      (run_extcodecopy run_InterpreterTypes_for_WIRE run_Host_for_H ref_interpreter ref_host)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
Opaque Impl_Eip7702CodeLoad.into_components.
  with_strategy transparent [run_extcodecopy] unfold extcodecopy, run_extcodecopy; cbn.
  popn_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t _ _ |- _ =>
    destruct array as [[address [memory_offset [code_offset [len []]]]]]
  end.
  s. {
    apply Impl_IntoAddress_for_U256.into_address_eq.
  }
  s. {
    apply HostEq.
  }
  destruct _.(Host.code) as [[code|] ?host]; cbn. 2: {
    s. {
      apply InterpreterTypesEq.
    }
    s.
  }
  as_usize_or_fail_macro_eq InterpreterTypesEq.
  s. {
    apply Impl_Eip7702CodeLoad.into_components_eq.
  }
  destruct Impl_Eip7702CodeLoad.into_components as [?code ?load]; cbn.
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply calc.extcodecopy_cost_eq.
  }
  gas_macro_eq idtac.
  s.
  destruct (_ =? 0); cbn; [s|].
  as_usize_or_fail_macro_eq InterpreterTypesEq.
  eapply Run.Let with (result :=
    (Output.Success (Z.min
      (i[as_usize_saturated_macro code_offset] mod 2^64)
      i[Impl_Bytes.len _.(Bytes.value)] : usize
    ), _)
  ). {
    unfold as_usize_saturated_macro, as_u64_saturated_macro; cbn.
    s. {
      s_apply Impl_Uint.as_limbs_eq.
    }
    s.
    destruct (_ && _) in |- *; cbn.
    { s. {
        apply Impl_usize.max_eq.
      }
      s. {
        apply simulate.mod.Impl_Deref_for_Bytes.Eq.I.
      }
      s. {
        s_apply Impl_Bytes.len_eq.
      }
      s. {
        apply Impl_Ord_for_usize.toplevel_min_eq.
      }
      s.
    }
    { s. {
        apply Impl_u64.max_eq.
      }
      s. {
        apply Impl_usize.max_eq.
      }
      s. {
        apply simulate.mod.Impl_Deref_for_Bytes.Eq.I.
      }
      s. {
        s_apply Impl_Bytes.len_eq.
      }
      s. {
        apply Impl_Ord_for_usize.toplevel_min_eq.
      }
      s.
    }
  }
  resize_memory_macro_eq InterpreterTypesEq.
  s. {
    apply simulate.mod.Impl_Deref_for_Bytes.Eq.I.
  }
  s. {
    apply Impl_Deref_for_Bytes.Eq.I.
  }
  s. {
    s_apply InterpreterTypesEq.
  }
  s; now destruct _.(MemoryTrait.resize).
Transparent Impl_Eip7702CodeLoad.into_components.
Qed.
