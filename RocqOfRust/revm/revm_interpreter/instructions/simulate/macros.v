Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import RocqOfRust.lib.simulate.lib.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import revm.revm_specification.simulate.hardfork.
Require Import ruint.links.lib.

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
