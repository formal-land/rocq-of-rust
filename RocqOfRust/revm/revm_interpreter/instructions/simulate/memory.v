Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.ops.simulate.deref.
Require Import core.simulate.option.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.memory.
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

Definition mload
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  popn_top_macro interpreter 0 id (fun _ top interpreter =>
  let top := top.(RefStub.projection) interpreter.(Interpreter.stack) in
  as_usize_or_fail_macro interpreter top None id (fun offset interpreter =>
  resize_memory_macro interpreter offset 32 id (fun interpreter =>
      (* let IInterpreterTypes := _ in
      let memory_synthetic :=
        IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.slice_len)
          interpreter.(Interpreter.memory) offset 32 in
      let deref_stub :=
        IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.Deref_for_Synthetic1).(Deref.deref) in
      let bytes := deref_stub.(RefStub.projection) memory_synthetic in
      let value := u256_from_be_bytes bytes in
      let stack := top.(RefStub.injection) interpreter.(Interpreter.stack) value in
      interpreter <| Interpreter.stack := stack |> *)
    interpreter
    )))).

Lemma mload_eq
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
      (run_mload run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        mload interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  unfold mload.
  gas_macro_eq InterpreterTypesEq.
  popn_top_macro_eq InterpreterTypesEq.
  as_usize_or_fail_macro_eq InterpreterTypesEq.
  resize_memory_macro_eq InterpreterTypesEq.
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    s_apply Impl_Uint.try_from_be_slice_eq.
  }
  s. {
    apply Impl_Option.unwrap_eq.
    admit.
  }
  s.
Admitted.

Definition mstore
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  popn_macro interpreter {| Integer.value := 2 |} id (fun arr interpreter =>
    let '⟬ offset_u256; value ⟭ := arr.(array.value) in
    as_usize_or_fail_ret_macro interpreter offset_u256 None id (fun offset interpreter =>
    resize_memory_macro interpreter offset 32 id (fun interpreter =>
      let IInterpreterTypes := _ in
      let bytes := u256_to_be_bytes_32 value in
      let memory :=
        IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.set)
          interpreter.(Interpreter.memory) offset bytes in
      interpreter <| Interpreter.memory := memory |>
    )))).

Lemma mstore_eq
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
      (run_mstore run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        mstore interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
Admitted.

Definition mstore8
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  popn_macro interpreter {| Integer.value := 2 |} id (fun arr interpreter =>
    let '⟬ offset_u256; value ⟭ := arr.(array.value) in
    as_usize_or_fail_ret_macro interpreter offset_u256 None id (fun offset interpreter =>
    resize_memory_macro interpreter offset 1 id (fun interpreter =>
      let IInterpreterTypes := _ in
      let byte : u8 := {| Integer.value := value.(Uint.value) mod 256 |} in
      let memory :=
        IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.set)
          interpreter.(Interpreter.memory) offset [byte] in
      interpreter <| Interpreter.memory := memory |>
    )))).

Lemma mstore8_eq
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
      (run_mstore8 run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        mstore8 interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
Admitted.

Definition msize
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.BASE id (fun interpreter =>
    let IInterpreterTypes := _ in
    let size :=
      IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.size)
        interpreter.(Interpreter.memory) in
    let value : aliases.U256.t := {| Uint.value := i[size] |} in
    push_macro interpreter value id (fun interpreter => interpreter)).

Lemma msize_eq
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
      (run_msize run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        msize interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  unfold msize.
  gas_macro_eq InterpreterTypesEq.
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    s_apply Impl_Uint.from_eq.
  }
  push_macro_eq InterpreterTypesEq.
  s.
Qed.

Definition mcopy
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  check_macro interpreter SpecId.CANCUN id (fun interpreter =>
  popn_macro interpreter {| Integer.value := 3 |} id (fun arr interpreter =>
    let '⟬ dst_u256; src_u256; len_u256 ⟭ := arr.(array.value) in
    as_usize_or_fail_ret_macro interpreter len_u256 None id (fun len interpreter =>
      if i[len] =? 0 then
        interpreter
      else
        as_usize_or_fail_ret_macro interpreter dst_u256 None id (fun dst interpreter =>
        as_usize_or_fail_ret_macro interpreter src_u256 None id (fun src interpreter =>
          let words_num := num_words len in
          let copy_cost : u64 := {| Integer.value := i[constants.VERYLOW] + i[words_num] * i[constants.COPY] |} in
          gas_macro interpreter copy_cost id (fun interpreter =>
            let max_offset : usize := {| Integer.value := Z.max i[dst] i[src] |} in
            resize_memory_macro interpreter max_offset len id (fun interpreter =>
              let IInterpreterTypes := _ in
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
Admitted.
