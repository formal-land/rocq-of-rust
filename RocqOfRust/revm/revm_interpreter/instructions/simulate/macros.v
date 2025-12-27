Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import revm.revm_specification.simulate.hardfork.

Definition gas_macro {WIRE K : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (cost : U64.t)
    (k_exit : Interpreter.t WIRE WIRE_types -> K)
    (k : Interpreter.t WIRE WIRE_types -> K) :
    K :=
  let gas :=
    IInterpreterTypes
        .(InterpreterTypes.Loop)
        .(Loop.gas)
        .(RefStub.projection)
      interpreter.(Interpreter.control) in
  match Impl_Gas.record_cost gas cost with
  | None =>
    let control :=
      IInterpreterTypes
          .(InterpreterTypes.Loop)
          .(Loop.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.OutOfGas in
    let interpreter := interpreter
      <| Interpreter.control := control |> in
    k_exit interpreter
  | Some gas =>
    let control :=
      IInterpreterTypes
          .(InterpreterTypes.Loop)
          .(Loop.gas)
          .(RefStub.injection)
        interpreter.(Interpreter.control) gas in
    let interpreter :=
      interpreter
        <| Interpreter.control := control |> in
    k interpreter
  end.

Ltac gas_macro_eq H gas set_instruction_result :=
  unfold gas_macro;
  eapply Run.Call; [
    apply gas
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
  [|
    eapply Run.Call; [
      apply Run.Pure
    |];
    eapply Run.Call; [
      apply (set_instruction_result _ _ instruction_result.InstructionResult.OutOfGas)
    |];
    apply Run.Pure
  ].

Definition popn_macro {WIRE K : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (N : Usize.t)
    (k_exit : Interpreter.t WIRE WIRE_types -> K)
    (k : array.t aliases.U256.t N -> Interpreter.t WIRE WIRE_types -> K) :
    K :=
    let stack := interpreter.(Interpreter.stack) in
    let (result, stack) :=
      IInterpreterTypes.(InterpreterTypes.Stack).(Stack.popn) N stack in
    let interpreter :=
      interpreter
        <| Interpreter.stack := stack |> in
    match result with
    | Some arr => k arr interpreter
    | None =>
      let control :=
        IInterpreterTypes.(InterpreterTypes.Loop).(Loop.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.StackUnderflow in
      let interpreter := interpreter
        <| Interpreter.control := control |> in
      k_exit interpreter
    end.

Ltac popn_macro_eq H IInterpreterTypes popn set_instruction_result :=
  unfold popn_macro;
  eapply Run.Call; [
    apply popn
  |];
  destruct IInterpreterTypes.(InterpreterTypes.Stack).(Stack.popn) as [[|] ?]; cbn; [|
    eapply Run.Call; [
      apply (set_instruction_result
        _
        _
        instruction_result.InstructionResult.StackUnderflow
      )
    |];
    cbn;
    apply Run.Pure
  ].

Definition popn_top_macro {WIRE K : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (N : Usize.t)
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
        .(InterpreterTypes.Stack)
        .(Stack.popn_top)
      N stack in
  let interpreter :=
    interpreter
      <| Interpreter.stack := stack |> in
  match result with
  | Some (arr, top) =>
    k arr top interpreter
  | None =>
    let control :=
      IInterpreterTypes.(InterpreterTypes.Loop).(Loop.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.StackUnderflow in
    let interpreter := interpreter
      <| Interpreter.control := control |> in
    k_exit interpreter
  end.

Ltac popn_top_macro_eq H IInterpreterTypes popn_top set_instruction_result :=
  unfold popn_top_macro;
  eapply Run.Call; [
    apply Run.Pure
  |];
  eapply Run.Call; [
    apply popn_top
  |];
  destruct IInterpreterTypes.(InterpreterTypes.Stack).(Stack.popn_top) as [[[? ?]|] ?];
  [|
    eapply Run.Call; [
      apply (set_instruction_result
        _
        _
        instruction_result.InstructionResult.StackUnderflow
      )
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
          .(InterpreterTypes.RuntimeFlag)
          .(SRuntimeFlag.spec_id)
        interpreter.(Interpreter.runtime_flag)
      )
      min
  then
    k interpreter
  else
    let control :=
      IInterpreterTypes
          .(InterpreterTypes.Loop)
          .(Loop.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.NotActivated in
    let interpreter :=
      interpreter
        <| Interpreter.control := control |> in
    k_exit interpreter.

Ltac check_macro_eq spec_id set_instruction_result :=
  unfold check_macro; cbn;
  eapply Run.Call; [
    apply spec_id
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
    eapply Run.Call; [
      apply (set_instruction_result _ _ instruction_result.InstructionResult.NotActivated)
    |];
    cbn;
    apply Run.Pure
  ].
