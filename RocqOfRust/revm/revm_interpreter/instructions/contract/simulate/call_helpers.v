Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.num.simulate.mod.
Require Import core.ops.links.range.
Require Import core.ops.simulate.deref.
Require Import core.ops.simulate.range.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.instructions.contract.links.call_helpers.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.interpreter.simulate.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import ruint.simulate.lib.

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
    option (Bytes.t * Range.t usize) * Interpreter.t WIRE WIRE_types :=
  popn_macro interpreter {| Integer.value := 4 |}
    (fun interpreter => (None, interpreter))
    (fun arr interpreter =>
  let '⟬ in_offset; in_len; out_offset; out_len ⟭ := arr.(array.value) in

  let '(in_range_opt, interpreter) := resize_memory interpreter in_offset in_len in
  match in_range_opt with
  | None => (None, interpreter)
  | Some in_range =>

  let input :=
    if Impl_Range.is_empty in_range then
      Impl_Bytes.new
    else
      let slice :=
        IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.slice)
            interpreter.(Interpreter.memory)
            in_range in
      let slice : list u8 :=
        IInterpreterTypes
          .(InterpreterTypes.MemoryTrait_for_Memory)
          .(MemoryTrait.Deref_for_Synthetic)
          .(Deref.deref)
          .(RefStub.projection)
          slice in
      Impl_Bytes.copy_from_slice slice in

  let '(ret_range_opt, interpreter) := resize_memory interpreter out_offset out_len in
  match ret_range_opt with
  | None => (None, interpreter)
  | Some ret_range =>
  (Some (input, ret_range), interpreter)

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

Definition calc_call_gas
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {IRuntimeFlag : RuntimeFlag.C WIRE_types.(InterpreterTypes.Types.RuntimeFlag)}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (account_load : AccountLoad.t)
    (has_transfer : bool)
    (local_gas_limit : u64) :
    option u64 * Interpreter.t WIRE WIRE_types :=
  let spec_id := IRuntimeFlag.(RuntimeFlag.spec_id) interpreter.(Interpreter.runtime_flag) in
  let call_cost := call_cost spec_id has_transfer account_load in
  gas_macro interpreter call_cost
    (fun interpreter => (None, interpreter))
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
      Z.min i[remaining] i[local_gas_limit] : u64
    else
      local_gas_limit in

  (Some gas_limit, interpreter)
  ).

Lemma calc_call_gas_eq
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    `{IInterpreterTypes : !InterpreterTypes.C WIRE_types}
    `{InterpreterTypesEq :
      !InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (account_load : AccountLoad.t)
    (has_transfer : bool)
    (local_gas_limit : u64)
    (stack : Stack.t) :
  let ref_interpreter := make_ref 0 in
  {{
    SimulateM.eval_f (
      run_calc_call_gas
        run_InterpreterTypes_for_WIRE
        ref_interpreter
        account_load
        has_transfer
        local_gas_limit
    )
    (interpreter :: stack)%stack 🌲
    let result_interpreter := calc_call_gas interpreter account_load has_transfer local_gas_limit in
    (
      Output.Success (fst result_interpreter),
      (snd result_interpreter :: stack)%stack
    )
  }}.
Proof.
Admitted.
