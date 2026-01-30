Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.num.simulate.mod.
Require Import core.simulate.result.
Require Import revm.revm_interpreter.interpreter.simulate.shared_memory.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import revm.revm_specification.simulate.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.lib.

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

Ltac gas_macro_eq InterpreterTypesEq :=
  unfold gas_macro;
  apply Run.LetUnfold;
  eapply Run.Call; [
    apply InterpreterTypesEq
      .(InterpreterTypes.Eq.LoopControl_for_Control)
      .(LoopControl.Eq.gas)
  |];
  try (eapply Run.Call; [
    apply Run.Pure
  |]);
  eapply Run.Call; [
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
  ].

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
    cbn;
    apply Run.Pure
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
    let control :=
      IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.StackUnderflow in
    let interpreter := interpreter
      <| Interpreter.control := control |> in
    k_exit interpreter
  end.

Ltac popn_top_macro_eq InterpreterTypesEq :=
  unfold popn_top_macro;
  eapply Run.Call; [
    apply Run.Pure
  |];
  eapply Run.Call; [
    apply InterpreterTypesEq
      .(InterpreterTypes.Eq.StackTrait_for_Stack)
      .(StackTrait.Eq.popn_top)
  |];
  destruct _.(InterpreterTypes.StackTrait_for_Stack).(StackTrait.popn_top) as [[[? ?]|] ?];
  [|
    apply Run.LetUnfold;
    eapply Run.Call; [
      apply InterpreterTypesEq
        .(InterpreterTypes.Eq.LoopControl_for_Control)
        .(LoopControl.Eq.set_instruction_result)
    |];
    apply Run.Pure
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
  Z.min v.(Uint.value) (2 ^ 64 - 1).

Definition as_usize_saturated_macro (v : aliases.U256.t) : usize :=
  Z.min v.(Uint.value) (2 ^ 64 - 1).

Definition as_usize_or_fail_ret_macro {WIRE K : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (v : aliases.U256.t)
    (reason_opt : option InstructionResult.t)
    (k_exit : Interpreter.t WIRE WIRE_types -> K)
    (k : usize -> Interpreter.t WIRE WIRE_types -> K) :
    K :=
  if v.(Uint.value) <=? (2 ^ 64 - 1) then
    k {| Integer.value := v.(Uint.value) |} interpreter
  else
    let reason :=
      match reason_opt with
      | Some reason => reason
      | None => instruction_result.InstructionResult.InvalidOperandOOG
      end in
    let control :=
      IInterpreterTypes
          .(InterpreterTypes.LoopControl_for_Control)
          .(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        reason in
    let interpreter := interpreter <| Interpreter.control := control |> in
    k_exit interpreter.

Ltac as_u64_saturated_macro_eq op1 :=
  eapply Run.Call; [
    apply Impl_Uint.as_limbs_eq; repeat unshelve econstructor
  |];
  repeat (cbn || apply Run.Pure || eapply Run.Call);
  destruct op1 as [op1]; cbn in *;
  assert (H_compares :
    (
      ((op1 / 2^64) mod 2^64 =? 0) &&
      ((op1 / 2^128) mod 2^64 =? 0) &&
      (op1 / 2^192 =? 0)
    ) = true ->
    op1 <= 2 ^ 64 - 1
  ) by lia;
  unfold Bool.eqb;
  destruct (_ && _) eqn:H_and_eq; cbn;
  [
    eapply Run.Call; [apply Run.Pure |];
    cbn;
    eapply Run.Call; [apply Impl_usize.max_eq |];
    cbn;
    eapply Run.Call; [apply Impl_Result_T_E.unwrap_or_eq |];
    cbn;
    apply Run.PureEq; repeat f_equal;
    replace (as_usize_saturated_macro _) with (op1 : usize); [
      unfold M.cast_integer; cbn;
      f_equal; [hauto lq: on|];
      lia
    |
      unfold as_usize_saturated_macro; cbn;
      now rewrite Z.min_l by lia
    ]
  |
    eapply Run.Call; [apply Impl_u64.max_eq |];
    cbn;
    eapply Run.Call; [cbn; apply Run.Pure |];
    eapply Run.Call; [apply Impl_usize.max_eq |];
    cbn;
    eapply Run.Call; [apply Impl_Result_T_E.unwrap_or_eq |];
    cbn;
    apply Run.PureEq; repeat f_equal;
    unfold M.cast_integer, as_usize_saturated_macro; cbn;
    f_equal; [hauto lq: on|];
    rewrite Z.min_r; [reflexivity|];
    assert (0 <= op1) by admit;
    lia
  ].

Definition resize_memory_macro {WIRE K : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (offset len : usize)
    (k_exit : Interpreter.t WIRE WIRE_types -> K)
    (k : Interpreter.t WIRE WIRE_types -> K) :
    K :=
  let words_num := num_words (Impl_usize.saturating_add offset len) in
  let '(resize_ok, memory) :=
    IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.resize)
      interpreter.(Interpreter.memory)
      {| Integer.value := words_num.(Integer.value) * 32 |} in
  let interpreter := interpreter <| Interpreter.memory := memory |> in
  if resize_ok then
    k interpreter
  else
    let control :=
      IInterpreterTypes.(InterpreterTypes.LoopControl_for_Control).(LoopControl.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.MemoryOOG in
    k_exit (interpreter <| Interpreter.control := control |>).
