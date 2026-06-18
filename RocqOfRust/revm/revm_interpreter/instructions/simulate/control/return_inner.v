Require Import simulate.RocqOfRust.
Require Import alloc.simulate.slice.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.convert.simulate.mod.
Require Import core.links.array.
Require Import core.ops.links.deref.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.control.return_inner.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.cmp.
Require Import ruint.simulate.from.
Require Import ruint.simulate.lib.

Definition return_inner
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (instruction_result : InstructionResult.t) :
    Interpreter.t WIRE WIRE_types :=
  popn_macro interpreter 2 id (fun _arr interpreter =>
  let '⟬ offset; len ⟭ := _arr.(array.value) in
  as_usize_or_fail_macro interpreter len None id (fun len interpreter =>
  (* We factorize the end of the function in [next] *)
  let next output interpreter :=
    let gas :=
      IInterpreterTypes
        .(InterpreterTypes.LoopControl_for_Control)
        .(LoopControl.gas)
        .(RefStub.projection)
        interpreter.(Interpreter.control) in
    let action :=
      interpreter_action.InterpreterAction.Return {|
        InterpreterResult.result := instruction_result;
        InterpreterResult.output := output;
        InterpreterResult.gas := gas;
      |} in
    let control :=
      IInterpreterTypes
        .(InterpreterTypes.LoopControl_for_Control)
        .(LoopControl.set_next_action)
        interpreter.(Interpreter.control)
        action
        instruction_result in
    interpreter <| Interpreter.control := control |> in
  if negb (i[len] =? 0) then
    as_usize_or_fail_macro interpreter offset None id (fun offset interpreter =>
    resize_memory_macro interpreter offset len id (fun interpreter =>
    let output :=
      IInterpreterTypes
        .(InterpreterTypes.MemoryTrait_for_Memory)
        .(MemoryTrait.slice_len)
        interpreter.(Interpreter.memory)
        offset len in
    let deref_stub :=
      IInterpreterTypes
        .(InterpreterTypes.MemoryTrait_for_Memory)
        .(MemoryTrait.Deref_for_Synthetic)
        .(deref.Deref.deref) in
    let output := deref_stub.(RefStub.projection) output in
    let output := Into.into (Impl_Slice.to_vec output) in
    next output interpreter
    ))
  else
    next Impl_Bytes.new interpreter
  )).

Lemma return_inner_eq
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (instruction_result : InstructionResult.t)
    (stack : Stack.t) :
  let ref_interpreter := make_ref 0 in
  {{
    SimulateM.eval_f
      (run_return_inner run_InterpreterTypes_for_WIRE ref_interpreter instruction_result)
      (interpreter :: stack)%stack 🌲
    (
      Output.Success tt,
      (return_inner interpreter instruction_result :: stack)%stack
    )
  }}.
Proof.
  intros.
  apply Run.remove_extra_stack1.
  with_strategy transparent [run_return_inner] unfold return_inner, run_return_inner; cbn.
  popn_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t aliases.U256.t _ |- _ =>
    destruct array as [[offset [len []]]]
  end.
  as_usize_or_fail_macro_eq InterpreterTypesEq.
  s. {
    apply simulate.mod.Impl_Default_for_Bytes.default_eq.
  }
  s; destruct negb; cbn.
  { as_usize_or_fail_macro_eq InterpreterTypesEq.
    resize_memory_macro_eq InterpreterTypesEq.
    s. {
      apply InterpreterTypesEq.
    }
    s. {
      apply InterpreterTypesEq.
    }
    s. {
      set (ref_self := Ref.cast_to _ _).
      apply (Impl_Slice.to_vec_eq _ ref_self); repeat unshelve econstructor.
    }
    s. {
      apply Impl_Into_for_From_T.Eq.I.
    }
    s. {
      apply InterpreterTypesEq.
    }
    s. {
      apply InterpreterTypesEq.
    }
    s.
    now destruct _.(MemoryTrait.resize).
  }
  { s. {
      apply InterpreterTypesEq.
    }
    s. {
      apply InterpreterTypesEq.
    }
    s.
  }
Qed.
