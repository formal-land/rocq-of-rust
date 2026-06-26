Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.interpreter_InterpreterResult.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.

Definition halt {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (result : instruction_result.InstructionResult.t) :
    Interpreter.t WIRE WIRE_types :=
  let action :=
    interpreter_action.InterpreterAction.Return {|
      InterpreterResult.result := result;
      InterpreterResult.output := Impl_Bytes.new;
      InterpreterResult.gas := interpreter.(Interpreter.gas);
    |} in
  interpreter
    <| Interpreter.bytecode :=
      IInterpreterTypes
        .(InterpreterTypes.LoopControl_for_Bytecode)
        .(LoopControl.set_action)
        interpreter.(Interpreter.bytecode)
        action
    |>.

Definition halt_oog {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  halt
    (interpreter <| Interpreter.gas := Impl_Gas.spend_all interpreter.(Interpreter.gas) |>)
    instruction_result.InstructionResult.OutOfGas.

Definition halt_fatal {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  halt interpreter instruction_result.InstructionResult.FatalExternalError.

Definition halt_memory_oog {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  halt interpreter instruction_result.InstructionResult.MemoryOOG.

Definition halt_underflow {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  halt interpreter instruction_result.InstructionResult.StackUnderflow.

Definition halt_overflow {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  halt interpreter instruction_result.InstructionResult.StackOverflow.

Definition halt_not_activated {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  halt interpreter instruction_result.InstructionResult.NotActivated.

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

Lemma halt_fatal_eq {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (stack_rest : Stack.t) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  {{
    SimulateM.eval_f
      (Impl_Interpreter.run_halt_fatal WIRE ref_interpreter)
      (interpreter :: stack_rest)%stack 🌲
    (
      Output.Success tt,
      (halt_fatal interpreter :: stack_rest)%stack
    )
  }}.
Proof.
  intros.
  unfold halt_fatal, halt.
  with_strategy transparent [
    Impl_Interpreter.run_halt_fatal
    Impl_Interpreter.run_halt
  ] unfold Impl_Interpreter.run_halt_fatal, Impl_Interpreter.run_halt.
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

Lemma halt_oog_eq {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (stack_rest : Stack.t) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  {{
    SimulateM.eval_f
      (Impl_Interpreter.run_halt_oog WIRE ref_interpreter)
      (interpreter :: stack_rest)%stack 🌲
    (
      Output.Success tt,
      (halt_oog interpreter :: stack_rest)%stack
    )
  }}.
Proof.
  intros.
  unfold halt_oog, halt.
  with_strategy transparent [
    Impl_Interpreter.run_halt_oog
    Impl_Interpreter.run_halt
  ] unfold Impl_Interpreter.run_halt_oog, Impl_Interpreter.run_halt.
  cbn.
  s.
  - apply Impl_Gas.spend_all_interpreter_eq.
  - repeat s.
    + apply Impl_Bytes.new_eq.
    + apply InterpreterTypesEq
        .(InterpreterTypes.Eq.LoopControl_for_Bytecode)
        .(LoopControl.BytecodeEq.set_action).
    + repeat rewrite Stack.dealloc_alloc_eq;
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

Lemma halt_overflow_eq {WIRE : Set} `{Link WIRE}
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
      InterpreterResult.result := instruction_result.InstructionResult.StackOverflow;
      InterpreterResult.output := Impl_Bytes.new;
      InterpreterResult.gas := interpreter.(Interpreter.gas);
    |} in
  {{
    SimulateM.eval_f
      (Impl_Interpreter.run_halt_overflow WIRE ref_interpreter)
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
    Impl_Interpreter.run_halt_overflow
    Impl_Interpreter.run_halt
  ] unfold Impl_Interpreter.run_halt_overflow, Impl_Interpreter.run_halt.
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

Lemma halt_not_activated_eq {WIRE : Set} `{Link WIRE}
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
      InterpreterResult.result := instruction_result.InstructionResult.NotActivated;
      InterpreterResult.output := Impl_Bytes.new;
      InterpreterResult.gas := interpreter.(Interpreter.gas);
    |} in
  {{
    SimulateM.eval_f
      (Impl_Interpreter.run_halt_not_activated WIRE ref_interpreter)
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
    Impl_Interpreter.run_halt_not_activated
    Impl_Interpreter.run_halt
  ] unfold Impl_Interpreter.run_halt_not_activated, Impl_Interpreter.run_halt.
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

Lemma halt_memory_oog_eq {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (stack_rest : Stack.t) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  {{
    SimulateM.eval_f
      (Impl_Interpreter.run_halt_memory_oog WIRE ref_interpreter)
      (interpreter :: stack_rest)%stack 🌲
    (
      Output.Success tt,
      (halt_memory_oog interpreter :: stack_rest)%stack
    )
  }}.
Proof.
  intros.
  unfold halt_memory_oog, halt.
  with_strategy transparent [
    Impl_Interpreter.run_halt_memory_oog
    Impl_Interpreter.run_halt
  ] unfold Impl_Interpreter.run_halt_memory_oog, Impl_Interpreter.run_halt.
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
