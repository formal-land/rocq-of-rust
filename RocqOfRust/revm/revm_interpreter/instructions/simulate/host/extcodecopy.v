Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import bytes.simulate.bytes.
Require Import core.links.array.
Require Import core.links.result.
Require Import core.num.simulate.mod.
Require Import core.simulate.option.
Require Import core.simulate.cmp.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_context_interface.simulate.journaled_state.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.host.extcodecopy.
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
Require Import revm.revm_bytecode.links.bytecode.
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
  let spec_id :=
    IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  as_usize_or_fail_ret_macro interpreter len_u256 None
    (fun interpreter => (interpreter, host)) (fun len interpreter =>
  let copy_cost :=
    match calc.copy_cost 0 len with
    | Some gas => gas
    | None => Impl_u64.MAX
    end in
  gas_macro interpreter copy_cost
    (fun interpreter => (interpreter, host)) (fun interpreter =>
  let memory_offset_usize := {| Integer.value := 0 |} in
  let '(memory_offset_usize, interpreter) :=
    if i[len] =? 0 then
      (memory_offset_usize, interpreter)
    else
      as_usize_or_fail_ret_macro interpreter memory_offset None
      (fun interpreter => (memory_offset_usize, interpreter)) (fun memory_offset interpreter =>
      resize_memory_macro interpreter memory_offset len
        (fun interpreter => (memory_offset, interpreter)) (fun interpreter =>
      (memory_offset, interpreter))) in
  let get_code interpreter host :=
    if Impl_SpecId.is_enabled_in spec_id SpecId.BERLIN then
      gas_macro interpreter WARM_STORAGE_READ_COST
        (fun interpreter => (None, interpreter, host)) (fun interpreter =>
      let skip_cold_load :=
        interpreter.(Interpreter.gas).(Gas.remaining).(Integer.value) <?
        COLD_ACCOUNT_ACCESS_COST_ADDITIONAL.(Integer.value) in
      let '(account_result, host) :=
        IHost.(Host.load_account_info_skip_cold_load) host address true skip_cold_load in
      match account_result with
      | Result.Ok account =>
          (if account.(AccountInfoLoad.is_cold) then
            gas_macro interpreter COLD_ACCOUNT_ACCESS_COST_ADDITIONAL
              (fun interpreter => (None, interpreter, host)) (fun interpreter =>
            (Some (account_info_load_original_bytes account), interpreter, host))
          else
            (Some (account_info_load_original_bytes account), interpreter, host))
      | Result.Err LoadError.ColdLoadSkipped =>
          (None, halt_oog interpreter, host)
      | Result.Err LoadError.DBError =>
          (None, halt_fatal interpreter, host)
      end)
    else
      let gas := if Impl_SpecId.is_enabled_in spec_id SpecId.TANGERINE then 700 else 20 in
      gas_macro interpreter gas
        (fun interpreter => (None, interpreter, host)) (fun interpreter =>
      let '(code_opt, host) := IHost.(Host.load_account_code) host address in
      match code_opt with
      | Some code => (Some code.(StateLoad.data), interpreter, host)
      | None => (None, halt_fatal interpreter, host)
      end) in
  let '(code_opt, interpreter, host) := get_code interpreter host in
  match code_opt with
  | None => (interpreter, host)
  | Some code =>
  let code_len := Impl_Bytes.len code.(Bytes.value) in
  let code_offset := Z.min (i[as_usize_saturated_macro code_offset] mod 2^64) i[code_len] in
  let memory :=
    IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.set_data)
      interpreter.(Interpreter.memory)
      memory_offset_usize
      code_offset
      len
      code.(Bytes.value).(bytes.Bytes.value) in
  (interpreter <| Interpreter.memory := memory |>, host)
  end))).

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
  let context := {|
    instruction_context.InstructionContext.interpreter := ref_interpreter;
    instruction_context.InstructionContext.host := ref_host;
  |} in
  let result := extcodecopy interpreter host in
  {{
    SimulateM.eval_f
      (run_extcodecopy run_InterpreterTypes_for_WIRE run_Host_for_H context)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
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
    apply InterpreterTypesEq.
  }
  as_usize_or_fail_macro_eq InterpreterTypesEq.
  s. {
    apply calc.copy_cost_eq.
  }
  s. {
    apply Impl_u64.max_eq.
  }
  gas_macro_eq idtac.
  s.
  destruct ((len.(lib.Uint.value) mod 2 ^ 64) mod 2 ^ 64 =? 0) eqn:?; cbn.
Admitted.
