Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.ops.simulate.deref.
Require Import core.simulate.cmp.
Require Import core.simulate.option.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.memory.mcopy.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.interpreter.simulate.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import revm.revm_specification.simulate.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.bytes.
Require Import ruint.simulate.from.

Definition mcopy
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{IInterpreterTypes : !InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  check_macro interpreter SpecId.CANCUN id (fun interpreter =>
  popn_macro interpreter {| Integer.value := 3 |} id (fun arr interpreter =>
  let '⟬ dst; src; len ⟭ := arr.(array.value) in
  as_usize_or_fail_ret_macro interpreter len None id (fun len interpreter =>
  gas_or_fail_macro interpreter (calc.copy_cost_verylow len) id (fun interpreter =>
  if i[len] =? 0 then
    interpreter
  else
    as_usize_or_fail_ret_macro interpreter dst None id (fun dst interpreter =>
    as_usize_or_fail_ret_macro interpreter src None id (fun src interpreter =>
    let max_offset : usize := {| Integer.value := Z.max i[dst] i[src] |} in
    resize_memory_macro interpreter max_offset len id (fun interpreter =>
    let memory :=
      IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.copy)
        interpreter.(Interpreter.memory) dst src len in
    interpreter <| Interpreter.memory := memory |>
  ))))))).

Lemma mcopy_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_host : '&mut H := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_mcopy run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        mcopy interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  with_strategy transparent [run_mcopy] unfold mcopy, run_mcopy; cbn.
  check_macro_eq InterpreterTypesEq.
  popn_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t aliases.U256.t _ |- _ =>
    destruct array as [[dst_u256 [src_u256 [len_u256 []]]]]
  end.
  as_usize_or_fail_macro_eq InterpreterTypesEq.
  s. {
    apply calc.copy_cost_verylow_eq.
  }
  unfold gas_macro.
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply Impl_Gas.record_cost_eq.
  }
  destruct Impl_Gas.record_cost. 2: {
    s. {
      apply InterpreterTypesEq.
    }
    s.
  }
  s.
  destruct (_ =? 0); [s|].
  as_usize_or_fail_macro_eq InterpreterTypesEq.
  as_usize_or_fail_macro_eq InterpreterTypesEq.
  s. {
    (* max *)
    s. {
      s. {
        s. {
          s. {
            s_apply Impl_Ord_for_usize.cmp_eq.
          }
          s.
        }
Admitted.
