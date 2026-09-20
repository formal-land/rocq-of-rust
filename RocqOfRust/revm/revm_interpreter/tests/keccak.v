From Stdlib Require Import List ZArith.

Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.tests.calls.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition empty_hash : Z :=
    89477152217924674838424037953991966239322087453347756267410168184682657981552.
  Definition run (code : list Z) := calls.Test.run code [].
  Definition result_kind (code : list Z) :=
    match run code with
    | Some (InterpreterAction.Return output, _) => Some output.(InterpreterResult.result)
    | _ => None
    end.

  Lemma empty_input :
    calls.Test.stack (run [96; 0; 96; 0; 32; 0]) = Some [empty_hash].
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_cost_is_thirty :
    calls.Test.remaining_gas (run [96; 0; 96; 0; 32; 0]) = Some 99964.
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_input_ignores_huge_offset :
    calls.Test.stack (run ([96; 0; 127] ++ List.repeat 255 32 ++ [32; 0])) = Some [empty_hash].
  Proof. vm_compute. reflexivity. Qed.

  Lemma real_nonempty_slice :
    calls.Test.stack (run
      [96; 97; 96; 5; 83; 96; 98; 96; 6; 83; 96; 99; 96; 7; 83;
       96; 3; 96; 5; 32; 0]) =
      Some [35286403120855365962805127237049809881669876751651884979611909062921250761797].
  Proof. vm_compute. reflexivity. Qed.

  Lemma expanded_memory_is_zero_filled :
    calls.Test.stack (run [96; 33; 96; 0; 32; 0]) =
      Some [110185045784767375427769874689313513947171322176640547528628348054121287848947].
  Proof. vm_compute. reflexivity. Qed.

  Lemma two_word_hash_and_memory_cost :
    calls.Test.remaining_gas (run [96; 33; 96; 0; 32; 0]) = Some 99946.
  Proof. vm_compute. reflexivity. Qed.

  Lemma word_rounding :
    (option_map Integer.value (keccak256_cost 31),
     option_map Integer.value (keccak256_cost 32),
     option_map Integer.value (keccak256_cost 33)) =
      (Some 36, Some 36, Some 42).
  Proof. vm_compute. reflexivity. Qed.

  Lemma maximum_length_uses_native_saturating_word_count :
    option_map Integer.value (keccak256_cost 18446744073709551615) =
      Some 3458764513820540952.
  Proof. vm_compute. reflexivity. Qed.

  Lemma gas_failure_precedes_allocation :
    result_kind [98; 47; 255; 255; 96; 0; 32; 0] = Some InstructionResult.OutOfGas.
  Proof. vm_compute. reflexivity. Qed.

  Lemma oversized_length_fails :
    result_kind ([127] ++ List.repeat 255 32 ++ [96; 0; 32; 0]) =
      Some InstructionResult.InvalidOperandOOG.
  Proof. vm_compute. reflexivity. Qed.

  Lemma nonempty_huge_offset_fails :
    result_kind ([96; 1; 127] ++ List.repeat 255 32 ++ [32; 0]) =
      Some InstructionResult.InvalidOperandOOG.
  Proof. vm_compute. reflexivity. Qed.

  Lemma memory_expansion_can_fail :
    result_kind [96; 1; 98; 16; 0; 0; 32; 0] = Some InstructionResult.MemoryOOG.
  Proof. vm_compute. reflexivity. Qed.

  Lemma missing_operand_fails :
    result_kind [96; 0; 32; 0] = Some InstructionResult.StackUnderflow.
  Proof. vm_compute. reflexivity. Qed.
End Test.
