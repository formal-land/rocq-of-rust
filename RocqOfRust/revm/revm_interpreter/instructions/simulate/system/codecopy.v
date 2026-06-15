Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import revm.revm_interpreter.instructions.links.system.codecopy.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.instructions.simulate.system.memory_resize.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.

Definition codecopy
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  popn_macro interpreter 3 id (fun arr interpreter =>
  let '⟬ memory_offset; code_offset; len ⟭ := arr.(array.value) in
  as_usize_or_fail_macro interpreter len None id (fun len interpreter =>
  let '(memory_offset_opt, interpreter) := memory_resize interpreter memory_offset len in
  match memory_offset_opt with
  | None => interpreter
  | Some memory_offset =>
    let code_offset := as_usize_saturated_macro code_offset in
    let bytecode :=
      IInterpreterTypes.(InterpreterTypes.LegacyBytecode_for_Bytecode).(LegacyBytecode.bytecode_slice)
        .(RefStub.projection) interpreter.(Interpreter.bytecode) in
    let memory :=
      IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.set_data)
        interpreter.(Interpreter.memory)
        memory_offset
        code_offset
        len
        bytecode in
    interpreter <| Interpreter.memory := memory |>
  end)).

Lemma codecopy_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref (A := H) 1 in
    {{
      SimulateM.eval_f
        (run_codecopy run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
        [interpreter; host]%stack 🌲
      (
        Output.Success tt,
        [codecopy interpreter; host]%stack
      )
    }}.
Proof.
Opaque memory_resize.
  with_strategy transparent [run_codecopy] unfold codecopy, run_codecopy; cbn.
  popn_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t aliases.U256.t _ |- _ =>
    destruct array as [[memory_offset [code_offset [len []]]]]
  end.
  as_usize_or_fail_macro_eq InterpreterTypesEq.
  s. {
    apply memory_resize_eq.
  }
  destruct memory_resize as [[?memory_offset|] ?interpreter]; cbn. 2: {
    s.
  }
  eapply Run.Let with (result := (Output.Success (as_usize_saturated_macro code_offset), _)). {
    as_usize_saturated_macro_eq.
  }
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    s_apply InterpreterTypesEq.
  }
  s.
Qed.
