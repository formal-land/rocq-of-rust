Require Import simulate.RocqOfRust.
Require Import core.simulate.option.
Require Import core.num.simulate.mod.
Require Import revm.revm_interpreter.interpreter.links.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.

Definition num_words (len : usize) : usize :=
  Impl_usize.saturating_add len 31 /i 32.

Lemma num_words_eq (len : usize) (stack : Stack.t) :
  {{
    SimulateM.eval_f (run_num_words len) stack 🌲
    (Output.Success (num_words len), stack)
  }}.
Proof.
  with_strategy transparent [run_num_words] unfold run_num_words.
  s. {
    apply Impl_usize.saturating_add_eq.
  }
  s.
Qed.

Definition resize_memory_cold
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{IInterpreterTypes : ! InterpreterTypes.C WIRE_types}
    (gas : Gas.t)
    (memory : WIRE_types.(InterpreterTypes.Types.Memory))
    (new_num_words : usize) :
    bool * (Gas.t * WIRE_types.(InterpreterTypes.Types.Memory)) :=
  let '(cost, memory_gas) :=
    Impl_MemoryGas.record_new_len gas.(Gas.memory) new_num_words in
  let gas := gas <| Gas.memory := memory_gas |> in
  match cost with
  | None =>
    (false, (gas, memory))
  | Some cost =>
    match Impl_Gas.record_cost gas cost with
    | None =>
      (false, (gas, memory))
    | Some gas =>
      let '(_, memory) :=
        IInterpreterTypes
          .(InterpreterTypes.MemoryTrait_for_Memory)
          .(MemoryTrait.resize)
          memory
          (new_num_words *i 32) in
      (true, (gas, memory))
    end
  end.

Definition resize_memory
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{IInterpreterTypes : ! InterpreterTypes.C WIRE_types}
    (gas : Gas.t)
    (memory : WIRE_types.(InterpreterTypes.Types.Memory))
    (offset len : usize) :
    bool * (Gas.t * WIRE_types.(InterpreterTypes.Types.Memory)) :=
  let new_num_words := num_words (Impl_usize.saturating_add offset len) in
  if i[new_num_words] >? i[gas.(Gas.memory).(MemoryGas.words_num)] then
    resize_memory_cold gas memory new_num_words
  else
    (true, (gas, memory)).

Lemma resize_memory_cold_eq
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    `{IInterpreterTypes : ! InterpreterTypes.C WIRE_types}
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (new_num_words : usize)
    (stack : Stack.t) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_gas : '&mut Gas.t := {| Ref.core :=
    SubPointer.Runner.apply
      ref_interpreter.(Ref.core)
      Interpreter.SubPointer.get_gas
  |} in
  let ref_memory : '&mut WIRE_types.(InterpreterTypes.Types.Memory) := {| Ref.core :=
    SubPointer.Runner.apply
      ref_interpreter.(Ref.core)
      Interpreter.SubPointer.get_memory
  |} in
  let result :=
    resize_memory_cold
      interpreter.(Interpreter.gas)
      interpreter.(Interpreter.memory)
      new_num_words in
  {{
    SimulateM.eval_f
      (run_resize_memory_cold
        run_InterpreterTypes_for_WIRE.(InterpreterTypes.run_MemoryTrait_for_Memory)
        ref_gas
        ref_memory
        new_num_words)
      (interpreter :: stack)%stack 🌲
    (
      Output.Success (fst result),
      (
        interpreter
          <| Interpreter.gas := fst (snd result) |>
          <| Interpreter.memory := snd (snd result) |>
        :: stack
      )%stack
    )
  }}.
Proof.
Admitted.

Lemma resize_memory_eq
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    `{IInterpreterTypes : ! InterpreterTypes.C WIRE_types}
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (offset len : usize)
    (stack : Stack.t) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_gas : '&mut Gas.t := {| Ref.core :=
    SubPointer.Runner.apply
      ref_interpreter.(Ref.core)
      Interpreter.SubPointer.get_gas
  |} in
  let ref_memory : '&mut WIRE_types.(InterpreterTypes.Types.Memory) := {| Ref.core :=
    SubPointer.Runner.apply
      ref_interpreter.(Ref.core)
      Interpreter.SubPointer.get_memory
  |} in
  let result :=
    resize_memory
      interpreter.(Interpreter.gas)
      interpreter.(Interpreter.memory)
      offset
      len in
  {{
    SimulateM.eval_f
      (run_resize_memory
        run_InterpreterTypes_for_WIRE.(InterpreterTypes.run_MemoryTrait_for_Memory)
        ref_gas
        ref_memory
        offset
        len)
      (interpreter :: stack)%stack 🌲
    (
      Output.Success (fst result),
      (
        interpreter
          <| Interpreter.gas := fst (snd result) |>
          <| Interpreter.memory := snd (snd result) |>
        :: stack
      )%stack
    )
  }}.
Proof.
Admitted.
