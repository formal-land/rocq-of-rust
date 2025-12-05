Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.arithmetic.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.simulate.add.
Require Import ruint.simulate.cmp.
Require Import ruint.simulate.div.
Require Import ruint.simulate.mul.

Definition gas_macro {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (cost : U64.t)
    (k : Interpreter.t WIRE WIRE_types -> Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
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
    interpreter
      <| Interpreter.control := control |>
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
  eapply Run.Call; [
    apply Run.Pure
  |];
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

Definition popn_top_macro {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (N : Usize.t)
    (k :
      array.t aliases.U256.t N ->
      RefStub.t WIRE_types.(InterpreterTypes.Types.Stack) aliases.U256.t ->
      Interpreter.t WIRE WIRE_types ->
      Interpreter.t WIRE WIRE_types
    ) :
    Interpreter.t WIRE WIRE_types :=
  let stack := interpreter.(Interpreter.stack) in
  let (result, stack) :=
    IInterpreterTypes
        .(InterpreterTypes.Stack)
        .(Stack.popn_top)
      N stack in
  match result with
  | Some (arr, top) =>
    let interpreter :=
      interpreter
        <| Interpreter.stack := stack |> in
    k arr top interpreter
  | None =>
    let control :=
      IInterpreterTypes.(InterpreterTypes.Loop).(Loop.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.StackUnderflow in
    interpreter
      <| Interpreter.control := control |>
      <| Interpreter.stack := stack |>
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

Lemma add_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_add run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        gas_macro interpreter constants.VERYLOW (fun interpreter =>
        popn_top_macro interpreter {| Integer.value := 1 |} (fun arr top interpreter =>
          let '{| ArrayPair.x := op1 |} := arr.(array.value) in
          let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
          let stack :=
            top.(RefStub.injection)
              interpreter.(Interpreter.stack) (Impl_Uint.wrapping_add op1 op2) in
          interpreter
            <| Interpreter.stack := stack |>
        ));
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  destruct InterpreterTypesEq as [[] []].
  cbn.
  gas_macro_eq H gas set_instruction_result.
  popn_top_macro_eq H IInterpreterTypes popn_top set_instruction_result.
  get_can_access.
  eapply Run.Call. {
    apply Impl_Uint.wrapping_add_eq.
  }
  get_can_access.
  apply Run.Pure.
Qed.
Global Opaque run_add.

Lemma mul_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_mul run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        gas_macro interpreter constants.LOW (fun interpreter =>
        popn_top_macro interpreter {| Integer.value := 1 |} (fun arr top interpreter =>
          let '{| ArrayPair.x := op1 |} := arr.(array.value) in
          let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
          let stack :=
            top.(RefStub.injection)
              interpreter.(Interpreter.stack) (Impl_Uint.wrapping_mul op1 op2) in
          interpreter
            <| Interpreter.stack := stack |>
        ));
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  destruct InterpreterTypesEq as [[] []].
  cbn.
  gas_macro_eq H gas set_instruction_result.
  popn_top_macro_eq H IInterpreterTypes popn_top set_instruction_result.
  get_can_access.
  eapply Run.Call. {
    apply Impl_Uint.wrapping_mul_eq.
  }
  get_can_access.
  apply Run.Pure.
Qed.
Global Opaque run_mul.

Lemma sub_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_sub run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        gas_macro interpreter constants.VERYLOW (fun interpreter =>
        popn_top_macro interpreter {| Integer.value := 1 |} (fun arr top interpreter =>
          let '{| ArrayPair.x := op1 |} := arr.(array.value) in
          let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
          let stack :=
            top.(RefStub.injection)
              interpreter.(Interpreter.stack) (Impl_Uint.wrapping_sub op1 op2) in
          interpreter
            <| Interpreter.stack := stack |>
        ));
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  destruct InterpreterTypesEq as [[] []].
  cbn.
  gas_macro_eq H gas set_instruction_result.
  popn_top_macro_eq H IInterpreterTypes popn_top set_instruction_result.
  get_can_access.
  eapply Run.Call. {
    apply Impl_Uint.wrapping_sub_eq.
  }
  get_can_access.
  apply Run.Pure.
Qed.
Global Opaque run_sub.

Lemma div_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_div run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        gas_macro interpreter constants.LOW (fun interpreter =>
        popn_top_macro interpreter {| Integer.value := 1 |} (fun arr top interpreter =>
          let '{| ArrayPair.x := op1 |} := arr.(array.value) in
          let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
          if Impl_Uint.is_zero op2 then
            interpreter
          else
            let stack :=
              top.(RefStub.injection)
                interpreter.(Interpreter.stack)
                (Impl_Uint.wrapping_div op1 op2) in
            interpreter
              <| Interpreter.stack := stack |>
        ));
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  destruct InterpreterTypesEq as [[] []].
  cbn.
  gas_macro_eq H gas set_instruction_result.
  popn_top_macro_eq H IInterpreterTypes popn_top set_instruction_result.
  cbn.
  eapply Run.Call; cbn. {
    setoid_rewrite (
      Impl_Uint.is_zero_like
        _
        (BITS := {| Integer.value := 256 |})
        (LIMBS := {| Integer.value := 4 |})
    ).
    cbn.
    get_can_access.
    apply Run.Pure.
  }
  cbn.
  eapply Run.Call; cbn. {
    apply Run.Pure.
  }
  cbn.
  eapply Run.Call; cbn. {
    apply Run.Pure.
  }
  cbn.
  destruct Impl_Uint.is_zero; cbn.
  { apply Run.Pure. }
  { progress repeat get_can_access.
    eapply Run.Call; cbn. {
      apply Impl_Uint.wrapping_div_eq.
    }
    cbn.
    progress repeat get_can_access.
    apply Run.Pure.
  }
Qed.
Global Opaque run_div.
