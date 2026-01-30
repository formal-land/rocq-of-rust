Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.num.simulate.mod.
Require Import core.ops.links.range.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_interpreter.instructions.contract.links.call_helpers.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.

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
    ( Some {|
        Range.start := offset;
        Range.end_ := {| Integer.value := offset.(Integer.value) + len.(Integer.value) |}
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
            ( Some {|
                Range.start := offset;
                Range.end_ := {| Integer.value := offset.(Integer.value) + len.(Integer.value) |}
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
  let result_interpreter := resize_memory interpreter offset len in
  {{
    SimulateM.eval_f (
      run_resize_memory run_InterpreterTypes_for_WIRE ref_interpreter offset len
    )
    (interpreter :: stack)%stack 🌲
    (
      Output.Success (fst result_interpreter),
      (snd result_interpreter :: stack)%stack
    )
  }}.
Proof.
Admitted.


Parameter get_memory_input_and_out_ranges :
  forall
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types},
  Interpreter.t WIRE WIRE_types ->
  option (Bytes.t * Range.t usize) *
  Interpreter.t WIRE WIRE_types.

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
  apply Run.remove_extra_stack1.
  with_strategy transparent [run_get_memory_input_and_out_ranges] unfold run_get_memory_input_and_out_ranges; cbn.
  idtac.
  unfold popn_macro;
  eapply Run.Call; [
    apply InterpreterTypesEq
      .(InterpreterTypes.Eq.StackTrait_for_Stack)
      .(StackTrait.Eq.popn)
  |];
  destruct _.(InterpreterTypes.StackTrait_for_Stack).(StackTrait.popn) as [[|] ?]; cbn; [|
    apply Run.LetUnfold;
    cbn;
    eapply Run.Call; [
      apply InterpreterTypesEq
        .(InterpreterTypes.Eq.LoopControl_for_Control)
        .(LoopControl.Eq.set_instruction_result)
    |];
    cbn
  ].
  2: {
    admit.
  }
Admitted.

Parameter calc_call_gas :
  forall
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types},
  Interpreter.t WIRE WIRE_types ->
  AccountLoad.t ->
  bool ->
  u64 ->
  option u64 * Interpreter.t WIRE WIRE_types.

Lemma calc_call_gas_eq
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
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
