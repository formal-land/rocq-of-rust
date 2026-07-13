Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.num.simulate.mod.
Require Import core.ops.links.range.
Require Import core.ops.simulate.deref.
Require Import core.ops.simulate.range.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.contract.links.call_helpers.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.interpreter.simulate.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import ruint.simulate.lib.

Parameter bytecode_of_account_load : StateLoad.t AccountLoad.t -> Bytecode.t.
Parameter bytecode_hash_of_account_load : StateLoad.t AccountLoad.t -> aliases.B256.t.

Definition resize_memory
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (offset len : aliases.U256.t) :
    option (Range.t usize) * Interpreter.t WIRE WIRE_types :=
  as_usize_or_fail_ret_macro interpreter len None
    (fun interpreter => (None, interpreter))
    (fun len interpreter =>
  if len.(Integer.value) =? 0 then
    let offset := Impl_usize.MAX in
    (
      Some {|
        Range.start := offset;
        Range.end_ := offset +i len;
      |},
      interpreter
    )
  else
    as_usize_or_fail_ret_macro interpreter offset None
      (fun interpreter => (None, interpreter))
      (fun offset interpreter =>
    resize_memory_macro interpreter offset len
      (fun interpreter => (None, interpreter))
      (fun interpreter =>
    (
      Some {|
        Range.start := offset;
        Range.end_ := offset +i len;
      |},
      interpreter
    )))).

Lemma resize_memory_eq
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (offset len : aliases.U256.t)
    (stack : Stack.t) :
  let ref_interpreter := make_ref 0 in
  let result := resize_memory interpreter offset len in
  {{
    SimulateM.eval_f (
      run_resize_memory run_InterpreterTypes_for_WIRE ref_interpreter offset len
    )
    (interpreter :: stack)%stack 🌲
    (
      Output.Success (fst result),
      (snd result :: stack)%stack
    )
  }}.
Proof.
  (* apply Run.remove_extra_stack1.
  with_strategy transparent [run_resize_memory] unfold run_resize_memory; cbn.
  unfold resize_memory.
  s. {
    apply Impl_Uint.as_limbs_eq; repeat unshelve econstructor.
  }
  s. {
    apply Impl_usize.max_eq.
  }
  s.
  destruct Bool.eqb eqn:?; r. {
    lu. cw InterpreterTypesEq.
    admit.
  }
  lu. repeat cp.
  destruct Bool.eqb eqn:? in |-*; r.
  { lu. c. {
      apply Impl_Uint.as_limbs_eq; repeat unshelve econstructor.
    }
    lu. cw Impl_usize.max_eq.
    repeat cp.
    destruct Bool.eqb eqn:? in |-*; r. {
      lu. cw InterpreterTypesEq.
      admit.
    }
    (* resize_memory! *)
    lu.
    cw Impl_usize.saturating_add_eq.
    cw num_words_eq.
    lu.
    cw InterpreterTypesEq.
    cw @Impl_Gas.record_memory_expansion_eq.
    l. {
      cp.
      cw InterpreterTypesEq.
      p.
    }
    cp.
    pf.
    all: admit.
  }
  { c. {
      apply Impl_usize.max_eq.
    }
    cp.
    pf.
    all: admit.
  } *)
Admitted.

Definition get_memory_input_and_out_ranges
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    option (Range.t usize * Range.t usize) * Interpreter.t WIRE WIRE_types :=
  popn_macro interpreter {| Integer.value := 4 |}
    (fun interpreter => (None, interpreter))
    (fun arr interpreter =>
  let '⟬ in_offset; in_len; out_offset; out_len ⟭ := arr.(array.value) in

  let '(in_range_opt, interpreter) := resize_memory interpreter in_offset in_len in
  match in_range_opt with
  | None => (None, interpreter)
  | Some in_range =>

  let in_range :=
    if Impl_Range.is_empty in_range then
      in_range
    else
      let offset :=
        IInterpreterTypes
          .(InterpreterTypes.MemoryTrait_for_Memory)
          .(MemoryTrait.local_memory_offset)
          interpreter.(Interpreter.memory) in
      {|
        Range.start := Impl_usize.saturating_add in_range.(Range.start) offset;
        Range.end_ := Impl_usize.saturating_add in_range.(Range.end_) offset;
      |} in

  let '(ret_range_opt, interpreter) := resize_memory interpreter out_offset out_len in
  match ret_range_opt with
  | None => (None, interpreter)
  | Some ret_range =>
  (Some (in_range, ret_range), interpreter)

  end end).

Lemma get_memory_input_and_out_ranges_eq
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    `{IInterpreterTypes : !InterpreterTypes.C WIRE_types}
    `{InterpreterTypesEq :
      !InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (stack : Stack.t) :
  let ref_interpreter := make_ref 0 in
  {{
    SimulateM.eval_f (
      run_get_memory_input_and_out_ranges run_InterpreterTypes_for_WIRE ref_interpreter
    )
    (interpreter :: stack)%stack 🌲
    let result_interpreter := get_memory_input_and_out_ranges interpreter in
    (
      Output.Success (fst result_interpreter),
      (snd result_interpreter :: stack)%stack
    )
  }}.
Proof.
  (* apply Run.remove_extra_stack1.
  with_strategy transparent [run_get_memory_input_and_out_ranges]
    unfold run_get_memory_input_and_out_ranges, get_memory_input_and_out_ranges;
    cbn.
  popn_macro_eq InterpreterTypesEq.
  lu.
  cw @resize_memory_eq. *)
Admitted.

Definition load_acc_and_calc_gas
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H)
    (to : Address.t)
    (transfers_value create_empty_account : bool)
    (stack_gas_limit : u64) :
    option LoadAccAndCalcGasResult.t * Interpreter.t WIRE WIRE_types * H :=
  let spec_id :=
    IInterpreterTypes
      .(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
      .(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  let static_gas := calc_call_static_gas spec_id transfers_value in
  gas_macro interpreter static_gas
    (fun interpreter => (None, interpreter, host))
    (fun interpreter =>

  match IHost.(Host.load_account_delegated) host to with
  | (None, host) =>
    let control :=
      IInterpreterTypes
          .(InterpreterTypes.LoopControl_for_Control)
          .(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.FatalExternalError in
    let interpreter := interpreter <| Interpreter.control := control |> in
    (None, interpreter, host)
  | (Some account_load, host) =>

  let dynamic_gas := warm_cold_cost_with_delegation account_load in
  gas_macro interpreter dynamic_gas
    (fun interpreter => (None, interpreter, host))
    (fun interpreter =>

  let gas_limit :=
    if Impl_SpecId.is_enabled_in spec_id SpecId.TANGERINE then
      let gas :=
        IInterpreterTypes
          .(InterpreterTypes.LoopControl_for_Control)
          .(LoopControl.gas)
          .(RefStub.projection)
          interpreter.(Interpreter.control) in
      let remaining := Impl_Gas.remaining_63_of_64_parts gas in
      Z.min i[remaining] i[stack_gas_limit] : u64
    else
      stack_gas_limit in
  gas_macro interpreter gas_limit
    (fun interpreter => (None, interpreter, host))
    (fun interpreter =>

  let gas_limit :=
    if transfers_value then
      Impl_u64.saturating_add gas_limit CALL_STIPEND
    else
      gas_limit in
  (
    Some {|
      LoadAccAndCalcGasResult.gas_limit := gas_limit;
      LoadAccAndCalcGasResult.bytecode := bytecode_of_account_load account_load;
      LoadAccAndCalcGasResult.bytecode_hash := bytecode_hash_of_account_load account_load;
    |},
    interpreter,
    host
  ))) end).

Lemma load_acc_and_calc_gas_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (run_Host_for_H : Host.Run H H_types)
    `{IInterpreterTypes : !InterpreterTypes.C WIRE_types}
    `{InterpreterTypesEq :
      !InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes}
    `{IHost : !Host.C H H_types}
    `{HostEq : !Host.Eq.t IHost}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H)
    (to : Address.t)
    (transfers_value create_empty_account : bool)
    (stack_gas_limit : u64)
    (stack : Stack.t) :
  let ref_context := make_ref (A := InstructionContext.t H WIRE WIRE_types) 0 in
  let ref_interpreter := make_ref (A := Interpreter.t WIRE WIRE_types) 1 in
  let ref_host := make_ref (A := H) 2 in
  let context := {|
    InstructionContext.interpreter := ref_interpreter;
    InstructionContext.host := ref_host;
  |} in
  {{
    SimulateM.eval_f (
      run_load_acc_and_calc_gas
        ref_context
        to
        transfers_value
        create_empty_account
        stack_gas_limit
    )
    (context :: interpreter :: host :: stack)%stack 🌲
    let '(result, interpreter, host) :=
      @load_acc_and_calc_gas
        WIRE
        H
        H0
        H1
        WIRE_types
        H2
        IInterpreterTypes
        H_types
        H3
        IHost
        interpreter
        host
        to
        transfers_value
        create_empty_account
        stack_gas_limit in
    (
      Output.Success result,
      (context :: interpreter :: host :: stack)%stack
    )
  }}.
Proof.
Admitted.
