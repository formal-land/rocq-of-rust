Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.num.simulate.mod.
Require Import core.simulate.result.
Require Import revm.revm_interpreter.interpreter.simulate.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.interpreter_InterpreterResult.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.lib.

Definition require_non_staticcall_macro {WIRE K : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (k_exit : Interpreter.t WIRE WIRE_types -> K)
    (k : Interpreter.t WIRE WIRE_types -> K) :
    K :=
  let is_static :=
    IInterpreterTypes
      .(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
      .(RuntimeFlag.is_static)
      interpreter.(Interpreter.runtime_flag) in
  if is_static then
    let control :=
      IInterpreterTypes
        .(InterpreterTypes.LoopControl_for_Control)
        .(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.StateChangeDuringStaticCall in
    let interpreter := interpreter <| Interpreter.control := control |> in
    k_exit interpreter
  else
    k interpreter.

Ltac require_non_staticcall_macro_eq InterpreterTypesEq :=
  unfold require_non_staticcall_macro;
  s; [
    apply InterpreterTypesEq
      .(InterpreterTypes.Eq.RuntimeFlag_for_RuntimeFlag)
      .(RuntimeFlag.Eq.is_static)
  |];
  destruct _.(RuntimeFlag.is_static); cbn; [
    s; [
      apply InterpreterTypesEq
        .(InterpreterTypes.Eq.LoopControl_for_Control)
        .(LoopControl.Eq.set_instruction_result)
    |];
    s
  |].

Definition gas_macro {WIRE K : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (cost : u64)
    (k_exit : Interpreter.t WIRE WIRE_types -> K)
    (k : Interpreter.t WIRE WIRE_types -> K) :
    K :=
  let gas :=
    IInterpreterTypes
        .(InterpreterTypes.LoopControl_for_Control)
        .(LoopControl.gas)
        .(RefStub.projection)
      interpreter.(Interpreter.control) in
  match Impl_Gas.record_cost gas cost with
  | None =>
    let control :=
      IInterpreterTypes
          .(InterpreterTypes.LoopControl_for_Control)
          .(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.OutOfGas in
    let interpreter := interpreter
      <| Interpreter.control := control |> in
    k_exit interpreter
  | Some gas =>
    let control :=
      IInterpreterTypes
          .(InterpreterTypes.LoopControl_for_Control)
          .(LoopControl.gas)
          .(RefStub.injection)
        interpreter.(Interpreter.control) gas in
    let interpreter :=
      interpreter
        <| Interpreter.control := control |> in
    k interpreter
  end.

Ltac gas_macro_eq gas_eq :=
  match goal with
  | InterpreterTypesEq : InterpreterTypes.Eq.t _ _ _ _ |- _ =>
  unfold gas_macro;
  s; [
    apply InterpreterTypesEq
      .(InterpreterTypes.Eq.LoopControl_for_Control)
      .(LoopControl.Eq.gas)
  |];
  gas_eq;
  s; [
    apply Impl_Gas.record_cost_eq
  |];
  destruct Impl_Gas.record_cost;
  (
    eapply Run.Call; [
      apply Run.Pure
    |]
  );
  cbn;
  [|
    eapply Run.Call; [
      apply Run.Pure
    |];
    apply Run.LetUnfold;
    eapply Run.Call; [
      apply InterpreterTypesEq
        .(InterpreterTypes.Eq.LoopControl_for_Control)
        .(LoopControl.Eq.set_instruction_result)
    |];
    cbn;
    apply Run.Pure
  ]
  end.

Definition gas_or_fail_macro {WIRE K : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (gas_opt : option u64)
    (k_exit : Interpreter.t WIRE WIRE_types -> K)
    (k : Interpreter.t WIRE WIRE_types -> K) :
    K :=
  match gas_opt with
  | None =>
    let control :=
      IInterpreterTypes
          .(InterpreterTypes.LoopControl_for_Control)
          .(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.OutOfGas in
    let interpreter := interpreter
      <| Interpreter.control := control |> in
    k_exit interpreter
  | Some gas_used =>
    gas_macro interpreter gas_used k_exit k
  end.

Ltac gas_or_fail_macro_eq :=
  match goal with
  | InterpreterTypesEq : InterpreterTypes.Eq.t _ _ _ _ |- _ =>
  step; [
    gas_macro_eq idtac |
    s; [
      apply InterpreterTypesEq
    |];
    s
  ]
  end.

Definition popn_macro {WIRE K : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (N : usize)
    (k_exit : Interpreter.t WIRE WIRE_types -> K)
    (k : array.t aliases.U256.t N -> Interpreter.t WIRE WIRE_types -> K) :
    K :=
    let stack := interpreter.(Interpreter.stack) in
    let (result, stack) :=
      IInterpreterTypes.(InterpreterTypes.StackTrait_for_Stack).(StackTrait.popn) N stack in
    let interpreter :=
      interpreter
        <| Interpreter.stack := stack |> in
    match result with
    | Some arr => k arr interpreter
    | None =>
      let control :=
        IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.StackUnderflow in
      let interpreter := interpreter
        <| Interpreter.control := control |> in
      k_exit interpreter
    end.

Ltac popn_macro_eq InterpreterTypesEq :=
  unfold popn_macro;
  s; [
    apply InterpreterTypesEq
  |];
  destruct _.(InterpreterTypes.StackTrait_for_Stack).(StackTrait.popn) as [[|] ?]; [|
    s; [
      apply InterpreterTypesEq
    |];
    s
  ].

Definition popn_top_macro {WIRE K : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (N : usize)
    (k_exit : Interpreter.t WIRE WIRE_types -> K)
    (k :
      array.t aliases.U256.t N ->
      RefStub.t WIRE_types.(InterpreterTypes.Types.Stack) aliases.U256.t ->
      Interpreter.t WIRE WIRE_types ->
      K
    ) :
    K :=
  let stack := interpreter.(Interpreter.stack) in
  let stack_len :=
    IInterpreterTypes
      .(InterpreterTypes.StackTrait_for_Stack)
      .(StackTrait.len)
      stack in
	  if i[stack_len] <? 1 + i[N] then
	    let action :=
	      interpreter_action.InterpreterAction.Return {|
	        InterpreterResult.result := instruction_result.InstructionResult.StackUnderflow;
	        InterpreterResult.output := Impl_Bytes.new;
	        InterpreterResult.gas := interpreter.(Interpreter.gas);
	      |} in
	    let bytecode :=
	      IInterpreterTypes
	        .(InterpreterTypes.LoopControl_for_Bytecode)
	        .(LoopControl.set_action)
	        interpreter.(Interpreter.bytecode)
	        action in
	    let interpreter :=
	      interpreter <| Interpreter.bytecode := bytecode |> in
	    k_exit interpreter
  else
    let (result, stack) :=
      IInterpreterTypes
          .(InterpreterTypes.StackTrait_for_Stack)
          .(StackTrait.popn_top)
        N stack in
    let interpreter :=
      interpreter
        <| Interpreter.stack := stack |> in
    match result with
    | Some (arr, top) =>
      k arr top interpreter
	    | None =>
	      k_exit interpreter
	    end.

Lemma stack_dealloc_cons_alloc_unit
    (A : Set)
    (value : A)
    (stack : Stack.t) :
  Stack.dealloc (value :: Stack.alloc stack tt)%stack =
  (value :: stack)%stack.
Proof.
  revert A value.
  induction stack as [|B head stack IH]; intros A value; cbn.
  { reflexivity. }
  {
    replace
      (match Stack.alloc stack tt with
       | []%stack => []%stack
       | (_ :: _)%stack => (head :: Stack.dealloc (Stack.alloc stack tt))%stack
       end)
      with (head :: stack)%stack.
    - specialize (IH B head).
      cbn in IH.
      rewrite IH.
      reflexivity.
    - specialize (IH B head).
      cbn in IH.
      symmetry.
      exact IH.
  }
Qed.

Lemma halt_eq {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (stack_rest : Stack.t)
    (result : instruction_result.InstructionResult.t) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let action :=
    interpreter_action.InterpreterAction.Return {|
      InterpreterResult.result := result;
      InterpreterResult.output := Impl_Bytes.new;
      InterpreterResult.gas := interpreter.(Interpreter.gas);
    |} in
  {{
    SimulateM.eval_f
      (Impl_Interpreter.run_halt WIRE ref_interpreter result)
      (interpreter :: stack_rest)%stack 🌲
    (
      Output.Success tt,
      (
        interpreter
          <| Interpreter.bytecode :=
            IInterpreterTypes
              .(InterpreterTypes.LoopControl_for_Bytecode)
              .(LoopControl.set_action)
              interpreter.(Interpreter.bytecode)
              action
          |>
        :: stack_rest
      )%stack
    )
  }}.
Proof.
  intros.
  with_strategy transparent [
    Impl_Interpreter.run_halt
  ] unfold Impl_Interpreter.run_halt.
  cbn.
  repeat s.
  - apply Impl_Bytes.new_eq.
  - apply InterpreterTypesEq
      .(InterpreterTypes.Eq.LoopControl_for_Bytecode)
      .(LoopControl.BytecodeEq.set_action).
  - repeat rewrite Stack.dealloc_alloc_eq;
    repeat rewrite stack_dealloc_cons_alloc_unit;
    reflexivity.
Qed.

Lemma halt_underflow_eq {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (stack_rest : Stack.t) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let action :=
    interpreter_action.InterpreterAction.Return {|
      InterpreterResult.result := instruction_result.InstructionResult.StackUnderflow;
      InterpreterResult.output := Impl_Bytes.new;
      InterpreterResult.gas := interpreter.(Interpreter.gas);
    |} in
  {{
    SimulateM.eval_f
      (Impl_Interpreter.run_halt_underflow WIRE ref_interpreter)
      (interpreter :: stack_rest)%stack 🌲
    (
      Output.Success tt,
      (
        interpreter
          <| Interpreter.bytecode :=
            IInterpreterTypes
              .(InterpreterTypes.LoopControl_for_Bytecode)
              .(LoopControl.set_action)
              interpreter.(Interpreter.bytecode)
              action
          |>
        :: stack_rest
      )%stack
    )
  }}.
Proof.
  intros.
  with_strategy transparent [
    Impl_Interpreter.run_halt_underflow
    Impl_Interpreter.run_halt
  ] unfold Impl_Interpreter.run_halt_underflow, Impl_Interpreter.run_halt.
  cbn.
  repeat s.
  - apply Impl_Bytes.new_eq.
  - apply InterpreterTypesEq
      .(InterpreterTypes.Eq.LoopControl_for_Bytecode)
      .(LoopControl.BytecodeEq.set_action).
  - repeat rewrite Stack.dealloc_alloc_eq;
    repeat rewrite stack_dealloc_cons_alloc_unit;
    reflexivity.
Qed.

Ltac popn_top_macro_eq InterpreterTypesEq :=
  unfold popn_top_macro;
  s; [
    apply InterpreterTypesEq
      .(InterpreterTypes.Eq.StackTrait_for_Stack)
      .(StackTrait.Eq.len)
  |];
  repeat s;
  destruct (_ <? _) eqn:?; cbn;
  [
    s; [
      eapply halt_underflow_eq;
      try exact InterpreterTypesEq
    |];
    repeat s
  |];
  eapply Run.Call; [
    apply InterpreterTypesEq
      .(InterpreterTypes.Eq.StackTrait_for_Stack)
      .(StackTrait.Eq.popn_top)
  |];
  cbn;
  destruct _.(InterpreterTypes.StackTrait_for_Stack).(StackTrait.popn_top) as [[[? ?]|] ?];
  [
    idtac
  |
    s
  ].

Definition push_macro {WIRE K : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (value : aliases.U256.t)
    (k_exit : Interpreter.t WIRE WIRE_types -> K)
    (k : Interpreter.t WIRE WIRE_types -> K) :
    K :=
  let '(success, stack) :=
    IInterpreterTypes.(InterpreterTypes.StackTrait_for_Stack).(StackTrait.push)
      interpreter.(Interpreter.stack) value in
  let interpreter := interpreter <| Interpreter.stack := stack |> in
  if success then k interpreter
  else
    let control :=
      IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.StackOverflow in
    let interpreter := interpreter <| Interpreter.control := control |> in
    k_exit interpreter.

Ltac push_macro_eq InterpreterTypesEq :=
  unfold push_macro;
  s; [
    apply InterpreterTypesEq
  |];
  destruct _.(InterpreterTypes.StackTrait_for_Stack).(StackTrait.push) as [[] ?]; [|
    s; [apply InterpreterTypesEq|];
    s
  ].

Definition check_macro {WIRE K : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (min : SpecId.t)
    (k_exit : Interpreter.t WIRE WIRE_types -> K)
    (k : Interpreter.t WIRE WIRE_types -> K) :
    K :=
  if
    Impl_SpecId.is_enabled_in
      (IInterpreterTypes
          .(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
          .(RuntimeFlag.spec_id)
        interpreter.(Interpreter.runtime_flag)
      )
      min
  then
    k interpreter
  else
    let control :=
      IInterpreterTypes
          .(InterpreterTypes.LoopControl_for_Control)
          .(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.NotActivated in
    let interpreter :=
      interpreter
        <| Interpreter.control := control |> in
    k_exit interpreter.

Ltac check_macro_eq InterpreterTypesEq :=
  unfold check_macro; cbn;
  apply Run.LetUnfold;
  eapply Run.Call; [
    apply InterpreterTypesEq
      .(InterpreterTypes.Eq.RuntimeFlag_for_RuntimeFlag)
      .(RuntimeFlag.Eq.spec_id)
  |];
  cbn;
  eapply Run.Call; [
    apply Impl_SpecId.is_enabled_in_eq
  |];
  cbn;
  eapply Run.Call; [
    apply Run.Pure
  |];
  cbn;
  eapply Run.Call; [
    apply Run.Pure
  |];
  cbn;
  destruct Impl_SpecId.is_enabled_in; cbn; [|
    apply Run.LetUnfold;
    cbn;
    eapply Run.Call; [
      apply InterpreterTypesEq
        .(InterpreterTypes.Eq.LoopControl_for_Control)
        .(LoopControl.Eq.set_instruction_result)
    |];
    cbn;
    apply Run.Pure
  ].

Definition as_u64_saturated_macro (v : aliases.U256.t) : u64 :=
  let v0 := v.(Uint.value) mod 2^64 in
  let v1 := (v.(Uint.value) / 2^64) mod 2^64 in
  let v2 := (v.(Uint.value) / 2^128) mod 2^64 in
  let v3 := (v.(Uint.value) / 2^192) mod 2^64 in
  if (v1 =? 0) && (v2 =? 0) && (v3 =? 0) then
    v0
  else
    Impl_u64.MAX.

Ltac as_u64_saturated_macro_eq :=
  unfold as_u64_saturated_macro;
  s; [
    s_apply Impl_Uint.as_limbs_eq
  |];
  s;
  (* In each branch of the [destruct], there are two possibilities depending on wether we called
     the [as_usize_saturated_macro_eq] macro or not. *)
  destruct (_ && _) in |- *; [
    (now s) ||
    (
      s; [
        apply Impl_usize.max_eq
      |];
      s;
      unfold M.cast_integer; cbn;
      f_equal; [hauto lq: on | lia]
    )
  | s; [
      apply Impl_u64.max_eq
    |];
    try (s; [
      apply Impl_usize.max_eq
    |]);
    s
  ].

Definition as_usize_saturated_macro (v : aliases.U256.t) : usize :=
  i[as_u64_saturated_macro v].

Ltac as_usize_saturated_macro_eq :=
  unfold as_usize_saturated_macro;
  as_u64_saturated_macro_eq.

Definition as_usize_or_fail_ret_macro {WIRE K : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (v : aliases.U256.t)
    (reason_opt : option InstructionResult.t)
    (k_exit : Interpreter.t WIRE WIRE_types -> K)
    (k : usize -> Interpreter.t WIRE WIRE_types -> K) :
    K :=
  let v0 := v.(Uint.value) mod 2^64 in
  let v1 := (v.(Uint.value) / 2^64) mod 2^64 in
  let v2 := (v.(Uint.value) / 2^128) mod 2^64 in
  let v3 := (v.(Uint.value) / 2^192) mod 2^64 in
  if (v0 >? i[Impl_usize.MAX]) || negb (v1 =? 0) || negb (v2 =? 0) || negb (v3 =? 0) then
    let reason :=
      match reason_opt with
      | Some reason => reason
      | None => instruction_result.InstructionResult.InvalidOperandOOG
      end in
    let action :=
      interpreter_action.InterpreterAction.Return {|
        InterpreterResult.result := reason;
        InterpreterResult.output := Impl_Bytes.new;
        InterpreterResult.gas := interpreter.(Interpreter.gas);
      |} in
    let bytecode :=
      IInterpreterTypes
          .(InterpreterTypes.LoopControl_for_Bytecode)
          .(LoopControl.set_action)
        interpreter.(Interpreter.bytecode)
        action in
    let interpreter := interpreter <| Interpreter.bytecode := bytecode |> in
    k_exit interpreter
  else
    k (M.cast_integer IntegerKind.Usize (v0 : u64)) interpreter.

Ltac as_usize_or_fail_ret_macro_eq InterpreterTypesEq :=
  unfold as_usize_or_fail_ret_macro;
  s; [
    s_apply Impl_Uint.as_limbs_eq
  |];
  s; [
    apply Impl_usize.max_eq
  |];
  s;
  destruct (_ || _); [
    s; [
      eapply halt_eq;
      try exact InterpreterTypesEq
    |];
    repeat s
  |].

Definition as_usize_or_fail_macro {WIRE K : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (v : aliases.U256.t)
    (reason_opt : option InstructionResult.t)
    (k_exit : Interpreter.t WIRE WIRE_types -> K)
    (k : usize -> Interpreter.t WIRE WIRE_types -> K) :
    K :=
  as_usize_or_fail_ret_macro interpreter v reason_opt k_exit k.

Ltac as_usize_or_fail_macro_eq InterpreterTypesEq :=
  unfold as_usize_or_fail_macro;
  as_usize_or_fail_ret_macro_eq InterpreterTypesEq.

Definition resize_memory_macro {WIRE K : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (offset len : usize)
    (k_exit : Interpreter.t WIRE WIRE_types -> K)
    (k : Interpreter.t WIRE WIRE_types -> K) :
    K :=
  let words_num := num_words (Impl_usize.saturating_add offset len) in
  let ref_gas :=
    IInterpreterTypes
      .(InterpreterTypes.LoopControl_for_Control)
      .(LoopControl.gas) in
  let gas := ref_gas.(RefStub.projection) interpreter.(Interpreter.control) in
  let '(extension_result, gas) := Impl_Gas.record_memory_expansion gas words_num in
  let interpreter :=
    interpreter <| Interpreter.control :=
      ref_gas.(RefStub.injection) interpreter.(Interpreter.control) gas
    |> in
  match extension_result with
  | MemoryExtensionResult.Extended =>
    let '(_, memory) :=
      IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.resize)
        interpreter.(Interpreter.memory) (words_num *i 32) in
    let interpreter := interpreter <| Interpreter.memory := memory |> in
    k interpreter
  | MemoryExtensionResult.OutOfGas =>
    let control :=
      IInterpreterTypes
          .(InterpreterTypes.LoopControl_for_Control)
          .(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.MemoryOOG in
    let interpreter := interpreter <| Interpreter.control := control |> in
    k_exit interpreter
  | MemoryExtensionResult.Same =>
    k interpreter
  end.

Ltac resize_memory_macro_eq InterpreterTypesEq :=
  unfold resize_memory_macro;
  cbn;
  repeat (apply Run.LetUnfold || cbn);
  eapply Run.Call; [
    apply Impl_usize.saturating_add_eq
  |];
  cbn;
  s; [
    apply num_words_eq
  |];
  s; [
    apply InterpreterTypesEq
  |];
  s; [
    apply InterpreterTypesEq
  |].
