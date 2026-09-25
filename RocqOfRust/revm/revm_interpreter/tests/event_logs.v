From Stdlib Require Import List ZArith.

Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.call_frame.
Require Import revm.revm_interpreter.tests.calls.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_interpreter.tests.static_calls.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition observe (result : option (InterpreterAction.t * CallFrame.state)) :=
    match result with
    | Some (_, state) => Some (StatefulHost.observe_logs
        (InstructionContext.State.host _ _ _ state))
    | None => None
    end.

  Definition entry (address : Z) (topics data : list Z) : StatefulHost.EvmLog.t :=
    {| StatefulHost.EvmLog.address := address;
       StatefulHost.EvmLog.topics := topics;
       StatefulHost.EvmLog.data := data |}.

  Definition emit (topics : list Z) : list Z :=
    List.flat_map (fun topic => [96; topic]) (List.rev topics) ++
      [96; 0; 96; 0; 160 + Z.of_nat (List.length topics)].

  Lemma all_topic_counts_and_order :
    List.map (fun topics => observe (calls.Test.run (emit topics ++ [0]) []))
      [[]; [1]; [1; 2]; [1; 2; 3]; [1; 2; 3; 4]] =
    List.map (fun topics => Some [entry 42 topics []])
      [[]; [1]; [1; 2]; [1; 2; 3]; [1; 2; 3; 4]].
  Proof. vm_compute. reflexivity. Qed.

  Lemma memory_slice_is_emitted :
    observe (calls.Test.run [96; 42; 96; 31; 83; 96; 1; 96; 31; 160; 0] []) =
      Some [entry 42 [] [42]].
  Proof. vm_compute. reflexivity. Qed.

  Lemma zero_filled_memory_and_expansion_gas :
    let result := calls.Test.run [96; 33; 96; 0; 160; 0] [] in
    (observe result, calls.Test.remaining_gas result) =
      (Some [entry 42 [] (List.repeat 0 33)], Some 99349).
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_log_cost :
    calls.Test.remaining_gas (calls.Test.run (emit [] ++ [0]) []) = Some 99619.
  Proof. vm_compute. reflexivity. Qed.

  Lemma each_topic_is_charged_once :
    List.map (fun topics => calls.Test.remaining_gas
      (calls.Test.run (emit topics ++ [0]) []))
      [[]; [1]; [1; 2]; [1; 2; 3]; [1; 2; 3; 4]] =
      List.map (@Some Z) [99619; 99241; 98863; 98485; 98107].
  Proof. vm_compute. reflexivity. Qed.

  Lemma per_topic_and_per_byte_cost :
    (option_map Integer.value (log_cost 0 0),
     option_map Integer.value (log_cost 4 32)) = (Some 375, Some 2131).
  Proof. vm_compute. reflexivity. Qed.

  Lemma checked_cost_overflow :
    log_cost 0 2305843009213693952 = None /\
    log_cost 0 2305843009213693951 = None /\
    log_cost 4 2305843009213693905 = None /\
    option_map Integer.value (log_cost 0 2305843009213693905) =
      Some 18446744073709551615.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Lemma empty_log_ignores_huge_offset :
    observe (calls.Test.run ([96; 0; 127] ++ List.repeat 255 32 ++ [160; 0]) []) =
      Some [entry 42 [] []].
  Proof. vm_compute. reflexivity. Qed.

  Lemma missing_topic_does_not_emit :
    let result := calls.Test.run [96; 0; 96; 0; 161; 0] [] in
    (static_calls.Test.result_kind result, observe result) =
      (Some InstructionResult.StackUnderflow, Some []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma insufficient_gas_does_not_emit :
    let result := calls.Test.run [97; 78; 32; 96; 0; 160; 0] [] in
    (static_calls.Test.result_kind result, observe result) =
      (Some InstructionResult.OutOfGas, Some []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma read_only_log_is_rejected :
    let result := static_calls.Test.run_static (emit [] ++ [0]) [] in
    (static_calls.Test.result_kind result, observe result) =
      (Some InstructionResult.StateChangeDuringStaticCall, Some []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma static_guard_precedes_stack_access :
    List.map (fun opcode => static_calls.Test.result_kind
      (static_calls.Test.run_static [opcode; 0] [])) [160; 161; 162; 163; 164] =
      List.repeat (Some InstructionResult.StateChangeDuringStaticCall) 5.
  Proof. vm_compute. reflexivity. Qed.

  Lemma memory_failure_does_not_emit :
    let result := calls.Test.run [96; 1; 98; 16; 0; 0; 160; 0] [] in
    (static_calls.Test.result_kind result, observe result) =
      (Some InstructionResult.MemoryOOG, Some []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma invalid_offset_does_not_emit :
    let result := calls.Test.run ([96; 1; 127] ++ List.repeat 255 32 ++ [160; 0]) [] in
    (static_calls.Test.result_kind result, observe result) =
      (Some InstructionResult.InvalidOperandOOG, Some []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma exceptional_halt_removes_prior_log :
    observe (calls.Test.run (emit [1] ++ [80]) []) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma child_address_and_log_order :
    observe (calls.Test.run
      (emit [1] ++ calls.Test.call 0 0 0 50000 ++ emit [3] ++ [0])
      (emit [2] ++ [0])) =
      Some [entry 42 [1] []; entry 43 [2] []; entry 42 [3] []].
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegatecall_uses_execution_address :
    observe (calls.Test.run
      [96; 0; 96; 0; 96; 0; 96; 0; 96; 43; 97; 195; 80; 244; 0]
      (emit [1] ++ [0])) = Some [entry 42 [1] []].
  Proof. vm_compute. reflexivity. Qed.

  Lemma child_revert_preserves_earlier_parent_log :
    observe (calls.Test.run
      (emit [1] ++ calls.Test.call 0 0 0 50000 ++ [0])
      (emit [2] ++ [96; 0; 96; 0; 253])) = Some [entry 42 [1] []].
  Proof. vm_compute. reflexivity. Qed.

  Lemma parent_revert_removes_successful_child_logs :
    observe (calls.Test.run
      (emit [1] ++ calls.Test.call 0 0 0 50000 ++ [96; 0; 96; 0; 253])
      (emit [2] ++ [0])) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma static_child_failure_leaves_parent_writable :
    let result := calls.Test.run
      (static_calls.Test.static_call 43 0 ++ emit [1] ++ [0]) (emit [2] ++ [0]) in
    (calls.Test.stack result, observe result) = (Some [0], Some [entry 42 [1] []]).
  Proof. vm_compute. reflexivity. Qed.
End Test.
