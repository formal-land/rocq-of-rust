Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.

Require Import revm.revm_interpreter.instructions.simulate.memory.mcopy.
Require Import revm.revm_interpreter.instructions.simulate.table.
Require Import revm.revm_interpreter.interpreter.links.runtime_flags.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.simulate.dispatch.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.dispatch.
Require Import revm.revm_interpreter.tests.host.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition run (spec : SpecId.t) (gas_limit : Z) (args contents : list Z) :=
    let interpreter : Interpreter.t WIRE WIRE_types :=
      make_interpreter {| Stack.value := List.map (fun x => {| Uint.value := x |}) args |} in
    let words := Z.of_nat (List.length contents) / 32 in
    let interpreter : Interpreter.t WIRE WIRE_types :=
      interpreter
        <| @Interpreter.runtime_flag WIRE _ WIRE_types _ := RuntimeFlags.non_static spec |>
        <| @Interpreter.memory WIRE _ WIRE_types _ :=
          {| Memory.value := List.map (fun x => {| Integer.value := x |}) contents;
             Memory.shared_buffer := [] |} |>
        <| @Interpreter.gas WIRE _ WIRE_types _ :=
          {| Gas.limit := {| Integer.value := gas_limit |};
             Gas.remaining := {| Integer.value := gas_limit |};
             Gas.refunded := (0 : i64);
             Gas.memory := {| MemoryGas.words_num := {| Integer.value := words |};
               MemoryGas.expansion_cost := {| Integer.value := 3 * words + words * words / 512 |} |} |} |> in
    mcopy interpreter.

  Definition observe (interpreter : Interpreter.t WIRE WIRE_types) :=
    (List.map Uint.value interpreter.(Interpreter.stack).(Stack.value),
     List.map Integer.value interpreter.(Interpreter.memory).(Memory.value),
     interpreter.(Interpreter.gas).(Gas.remaining).(Integer.value),
     match interpreter.(Interpreter.bytecode).(Bytecode.action) with
     | Some (InterpreterAction.Return result) => Some result.(InterpreterResult.result)
     | _ => None
     end).

  Definition seed : list Z := [1; 2; 3; 4; 5] ++ List.repeat 0 27.

  Lemma static_gas_is_zero : table_static_gas 94 = Some 0.
  Proof. vm_compute. reflexivity. Qed.

  Lemma dispatcher_charges_copy_base_once :
    List.map
      (fun spec => run_plain_stack_at spec (List.map byte [95; 95; 95; 94; 90; 0]))
      [SpecId.CANCUN; SpecId.PRAGUE] =
    [Some [{| Uint.value := 999989 |}]; Some [{| Uint.value := 999989 |}]].
  Proof. vm_compute. reflexivity. Qed.

  Lemma dispatcher_rejects_mcopy_before_cancun :
    let interpreter := interpreter_with_spec_id
      (make_interpreter_with_bytecode [byte 94] {| Stack.value := [] |})
      SpecId.SHANGHAI in
    let state : InstructionContext.State.t TestHost.t WIRE WIRE_types :=
      {| InstructionContext.State.interpreter := interpreter;
         InstructionContext.State.host := TestHost.Make |} in
    let table := FragmentInstructionTable.table
      (H := TestHost.t) (run_host := run_Host_for_TestHost)
      run_InterpreterTypes_for_WIRE in
    match InterpreterDispatch.run_plain_fuel 1 InterpreterTypes.I
      bytecode_is_not_end table state with
    | Some (InterpreterAction.Return result, _) => Some result.(InterpreterResult.result)
    | _ => None
    end = Some InstructionResult.NotActivated.
  Proof. vm_compute. reflexivity. Qed.

  Lemma shanghai_rejects_before_stack_or_gas_checks :
    observe (run SpecId.SHANGHAI 0 [] []) =
    ([], [], 0, Some InstructionResult.NotActivated).
  Proof. vm_compute. reflexivity. Qed.

  Lemma underflow_preserves_stack_and_gas :
    List.map (fun args => observe (run SpecId.CANCUN 100 args []))
      [[]; [1]; [1; 2]] =
    [([], [], 100, Some InstructionResult.StackUnderflow);
     ([1], [], 100, Some InstructionResult.StackUnderflow);
     ([1; 2], [], 100, Some InstructionResult.StackUnderflow)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma overlapping_copy_to_higher_offset_snapshots_source :
    observe (run SpecId.CANCUN 6 [1; 0; 4; 99] seed) =
    ([99], [1; 1; 2; 3; 4] ++ List.repeat 0 27, 0, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma overlapping_copy_to_lower_offset_snapshots_source :
    observe (run SpecId.PRAGUE 6 [0; 1; 4] seed) =
    ([], [2; 3; 4; 5; 5] ++ List.repeat 0 27, 0, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma copying_to_same_offset_preserves_bytes :
    observe (run SpecId.CANCUN 6 [0; 0; 32] seed) = ([], seed, 0, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma zero_length_ignores_maximal_offsets :
    observe (run SpecId.CANCUN 3 [2 ^ 256 - 1; 2 ^ 256 - 1; 0] []) =
    ([], [], 0, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma zero_length_preserves_allocated_memory :
    observe (run SpecId.PRAGUE 3 [2 ^ 256 - 1; 2 ^ 256 - 1; 0] seed) =
    ([], seed, 0, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma zero_length_still_requires_base_gas :
    observe (run SpecId.CANCUN 2 [0; 0; 0] []) =
    ([], [], 0, Some InstructionResult.OutOfGas).
  Proof. vm_compute. reflexivity. Qed.

  Lemma copy_word_cost_is_required_before_writing :
    observe (run SpecId.CANCUN 5 [1; 0; 1] seed) =
    ([], seed, 0, Some InstructionResult.OutOfGas).
  Proof. vm_compute. reflexivity. Qed.

  Lemma expansion_at_destination_charges_only_new_word :
    observe (run SpecId.CANCUN 9 [32; 0; 1] seed) =
    ([], seed ++ [1] ++ List.repeat 0 31, 0, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma expansion_at_source_reads_zero_bytes :
    observe (run SpecId.CANCUN 9 [0; 32; 1] seed) =
    ([], [0; 2; 3; 4; 5] ++ List.repeat 0 59, 0, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma expansion_failure_preserves_memory :
    observe (run SpecId.CANCUN 8 [32; 0; 1] seed) =
    ([], seed, 2, Some InstructionResult.MemoryOOG).
  Proof. vm_compute. reflexivity. Qed.

  Lemma copy_cost_rounds_up_at_word_boundary :
    observe (run SpecId.CANCUN 12 [0; 0; 33] seed) =
    ([], seed ++ List.repeat 0 32, 0, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_memory_expands_both_ranges_once :
    observe (run SpecId.PRAGUE 12 [32; 0; 1] []) =
    ([], List.repeat 0 64, 0, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma oversized_length_fails_before_gas_charge :
    observe (run SpecId.CANCUN 100 [0; 0; 2 ^ 64] []) =
    ([], [], 100, Some InstructionResult.InvalidOperandOOG).
  Proof. vm_compute. reflexivity. Qed.

  Lemma oversized_destination_fails_after_copy_gas :
    observe (run SpecId.CANCUN 100 [2 ^ 64; 0; 1] []) =
    ([], [], 94, Some InstructionResult.InvalidOperandOOG).
  Proof. vm_compute. reflexivity. Qed.

  Lemma oversized_source_fails_after_copy_gas :
    observe (run SpecId.CANCUN 100 [0; 2 ^ 64; 1] []) =
    ([], [], 94, Some InstructionResult.InvalidOperandOOG).
  Proof. vm_compute. reflexivity. Qed.

  Lemma maximal_destination_cannot_allocate :
    observe (run SpecId.CANCUN 100 [2 ^ 64 - 1; 0; 1] []) =
    ([], [], 94, Some InstructionResult.MemoryOOG).
  Proof. vm_compute. reflexivity. Qed.

  Lemma maximal_source_cannot_allocate :
    observe (run SpecId.CANCUN 100 [0; 2 ^ 64 - 1; 1] []) =
    ([], [], 94, Some InstructionResult.MemoryOOG).
  Proof. vm_compute. reflexivity. Qed.
End Test.
