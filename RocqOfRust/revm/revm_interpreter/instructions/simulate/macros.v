Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.num.simulate.mod.
Require Import core.simulate.result.
Require Import revm.revm_interpreter.interpreter.simulate.shared_memory.
Require Import revm.revm_interpreter.links.gas.
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
  c; [
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

(* TODO; for now we inline this tactic where it is used *)
(*
Ltac gas_or_fail_macro_eq InterpreterTypesEq :=
*)

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
  s; [
    apply InterpreterTypesEq
      .(InterpreterTypes.Eq.StackTrait_for_Stack)
      .(StackTrait.Eq.popn_top)
  |];
  destruct _.(InterpreterTypes.StackTrait_for_Stack).(StackTrait.popn_top) as [[[? ?]|] ?];
  [|
    s; [
      apply InterpreterTypesEq
        .(InterpreterTypes.Eq.LoopControl_for_Control)
        .(LoopControl.Eq.set_instruction_result)
    |];
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
  destruct (_ && _) in |- *; [
    s; [
      apply Impl_usize.max_eq
    |];
    s;
    unfold M.cast_integer; cbn;
    f_equal; [hauto lq: on | lia]
  | s; [
      apply Impl_u64.max_eq
    |];
    s; [
      apply Impl_usize.max_eq
    |];
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
  if (v0 >? i[Impl_usize.MAX]) || negb(v1 =? 0) || negb(v2 =? 0) || negb(v3 =? 0) then
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
      apply InterpreterTypesEq
    |];
    s
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
  s; [
    apply Impl_usize.saturating_add_eq
  |];
  s; [
    apply num_words_eq
  |];
  s; [
    apply InterpreterTypesEq
  |];
  s; [
    apply Impl_Gas.record_memory_expansion_eq
  |];
  s; [
    apply InterpreterTypesEq
  |].
