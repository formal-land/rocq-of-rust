From Stdlib Require Import List ZArith.

Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import bytes.links.bytes.
Require Import revm.revm_interpreter.interpreter.links.runtime_flags.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.call_frame.
Require Import revm.revm_interpreter.tests.call_runner.
Require Import revm.revm_interpreter.tests.calls.
Require Import revm.revm_interpreter.tests.identity_precompile.
Require Import revm.revm_interpreter.tests.precompile_frame.
Require Import revm.revm_interpreter.tests.stateful_dispatch.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_interpreter.tests.static_calls.
Require Import revm.revm_precompile.tests.bn254.
Require Import revm.revm_primitives.links.hardfork.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition call (opcode address value input_size output_offset output_size gas : Z) :=
    identity_precompile.Test.call opcode address value input_size output_offset output_size gas.

  Definition initial (program : list Z) : CallFrame.state :=
    let state := calls.Test.initial program [] in
    {| InstructionContext.State.interpreter := InstructionContext.State.interpreter _ _ _ state;
       InstructionContext.State.host := StatefulHost.warm_account
         (StatefulHost.warm_account (InstructionContext.State.host _ _ _ state) 6) 7 |}.

  Definition run (program : list Z) := CallRunner.run 300 (initial program).

  Definition owned_inputs (address : Z) (data : list Z) (gas : Z) : CallInputs.t :=
    identity_precompile.Test.owned_inputs
      <| CallInputs.input := CallInput.Bytes
        (Impl_Bytes.copy_from_slice (List.map StatefulHost.rust_byte data)) |>
      <| CallInputs.gas_limit := {| Integer.value := gas |} |>
      <| CallInputs.bytecode_address := StatefulHost.rust_address address |>
      <| CallInputs.target_address := StatefulHost.rust_address address |>.

  Definition direct (spec : SpecId.t) (multiply : bool) (data : list Z) (gas : Z) : InterpreterResult.t :=
    let parent := InstructionContext.State.interpreter _ _ _ (initial [0]) in
    let child := CallFrame.child parent (owned_inputs (if multiply then 7 else 6) data gas) [] in
    let child := stateful_dispatch.interpreter_with_spec_id child spec in
    PrecompileFrame.bn254 multiply child.

  Definition direct_observation (result : InterpreterResult.t) :=
    (result.(InterpreterResult.result),
     result.(InterpreterResult.gas).(Gas.remaining).(Integer.value),
     List.map Integer.value result.(InterpreterResult.output)
       .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value)).

  Lemma byzantium_add_cost :
    direct_observation (direct SpecId.BYZANTIUM false [] 500) =
    (InstructionResult.Return, 0, List.repeat 0 64).
  Proof. vm_compute. reflexivity. Qed.

  Lemma before_repricing_add_oog :
    direct_observation (direct SpecId.PETERSBURG false [] 150) =
    (InstructionResult.PrecompileOOG, 150, []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma istanbul_add_cost :
    direct_observation (direct SpecId.ISTANBUL false [] 150) =
    (InstructionResult.Return, 0, List.repeat 0 64).
  Proof. vm_compute. reflexivity. Qed.

  Lemma byzantium_mul_cost :
    direct_observation (direct SpecId.BYZANTIUM true [] 40000) =
    (InstructionResult.Return, 0, List.repeat 0 64).
  Proof. vm_compute. reflexivity. Qed.

  Lemma before_repricing_mul_oog :
    direct_observation (direct SpecId.PETERSBURG true [] 6000) =
    (InstructionResult.PrecompileOOG, 6000, []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma istanbul_mul_cost :
    direct_observation (direct SpecId.ISTANBUL true [] 6000) =
    (InstructionResult.Return, 0, List.repeat 0 64).
  Proof. vm_compute. reflexivity. Qed.

  Lemma invalid_point_maps_to_error :
    direct_observation (direct SpecId.ISTANBUL false revm.revm_precompile.tests.bn254.Test.malformed 150) =
    (InstructionResult.PrecompileError, 150, []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma byzantium_activation :
    (PrecompileFrame.is_precompile SpecId.SPURIOUS_DRAGON 6,
     PrecompileFrame.is_precompile SpecId.SPURIOUS_DRAGON 7,
     PrecompileFrame.is_precompile SpecId.BYZANTIUM 6,
     PrecompileFrame.is_precompile SpecId.BYZANTIUM 7,
     PrecompileFrame.supported 8) = (false, false, true, true, true).
  Proof. vm_compute. reflexivity. Qed.

  Definition generator_memory : list Z :=
    [96; 1; 96; 0; 82; 96; 2; 96; 32; 82].

  Definition scalar_one_memory : list Z := [96; 1; 96; 64; 82].

  Definition invalid_point_memory : list Z :=
    [96; 1; 96; 0; 82; 96; 1; 96; 32; 82].

  Definition output_memory (size : nat) result :=
    option_map (List.skipn 128) (calls.Test.memory_prefix (128 + size) result).

  Definition price (address : Z) := if address =? 6 then 150 else 6000.

  Definition input_size (address : Z) := if address =? 6 then 64 else 96.

  Definition input_memory (address : Z) := generator_memory ++
    (if address =? 6 then [] else scalar_one_memory).

  Lemma add_all_call_schemes_dispatch_to_address_six :
    List.map (fun opcode => let result := run (generator_memory ++
      call opcode 6 0 64 128 64 150 ++ [0]) in
      (calls.Test.stack result, calls.Test.returned_bytes result, output_memory 64 result))
      [241;242;244;250] =
    List.repeat (Some [1], Some revm.revm_precompile.tests.bn254.Test.generator,
      Some revm.revm_precompile.tests.bn254.Test.generator) 4.
  Proof. vm_compute. reflexivity. Qed.

  Lemma mul_all_call_schemes_dispatch_to_address_seven :
    List.map (fun opcode => let result := run (generator_memory ++ scalar_one_memory ++
      call opcode 7 0 96 128 64 6000 ++ [0]) in
      (calls.Test.stack result, calls.Test.returned_bytes result, output_memory 64 result))
      [241;242;244;250] =
    List.repeat (Some [1], Some revm.revm_precompile.tests.bn254.Test.generator,
      Some revm.revm_precompile.tests.bn254.Test.generator) 4.
  Proof. vm_compute. reflexivity. Qed.

  Lemma nested_exact_gas_boundary :
    List.map (fun address => List.map (fun opcode =>
      let result := run (call opcode address 0 0 0 0 (price address - 1) ++ [0]) in
      (calls.Test.stack result, calls.Test.returned_bytes result)) [241;242;244;250]) [6;7] =
    List.repeat (List.repeat (Some [0], Some []) 4) 2.
  Proof. vm_compute. reflexivity. Qed.

  Lemma short_return_copy_preserves_sentinels :
    List.map (fun address => let result := run (input_memory address ++
      [96;238;96;129;83;96;255;96;130;83] ++
      call 241 address 0 (input_size address) 128 1 (price address) ++ [0]) in
      (calls.Test.returned_bytes result, output_memory 3 result)) [6;7] =
    List.repeat (Some revm.revm_precompile.tests.bn254.Test.generator, Some [0;238;255]) 2.
  Proof. vm_compute. reflexivity. Qed.

  Lemma invalid_second_call_clears_data_preserves_previous_copy :
    List.map (fun address => let result := run (input_memory address ++
      call 241 address 0 (input_size address) 128 64 (price address) ++
      [96;1;96;32;82] ++
      call 241 address 0 (input_size address) 128 64 (price address) ++ [0]) in
      (calls.Test.stack result, calls.Test.returned_bytes result, output_memory 64 result)) [6;7] =
    List.repeat (Some [0;1], Some [], Some revm.revm_precompile.tests.bn254.Test.generator) 2.
  Proof. vm_compute. reflexivity. Qed.

  Lemma successful_call_transfers_value :
    List.map (fun address => let result := run
      (call 241 address 3 0 0 0 (price address) ++ [0]) in
      (calls.Test.stack result, calls.Test.balance 42 result, calls.Test.balance address result)) [6;7] =
    List.repeat (Some [1], Some 7, Some 3) 2.
  Proof. vm_compute. reflexivity. Qed.

  Lemma invalid_point_rolls_back_call_value :
    List.map (fun address => let result := run (invalid_point_memory ++
      call 241 address 3 64 0 0 (price address) ++ [0]) in
      (calls.Test.stack result, calls.Test.balance 42 result, calls.Test.balance address result)) [6;7] =
    List.repeat (Some [0], Some 10, Some 0) 2.
  Proof. vm_compute. reflexivity. Qed.

  Lemma mul_oog_rolls_back_value_despite_stipend :
    let result := run (call 241 7 3 0 0 0 0 ++ [0]) in
    (calls.Test.stack result, calls.Test.balance 42 result, calls.Test.balance 7 result) =
    (Some [0], Some 10, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma callcode_checks_value_without_transfer :
    List.map (fun address => let result := run
      (call 242 address 3 0 0 0 (price address) ++ [0]) in
      (calls.Test.stack result, calls.Test.balance 42 result, calls.Test.balance address result)) [6;7] =
    List.repeat (Some [1], Some 10, Some 0) 2.
  Proof. vm_compute. reflexivity. Qed.

  Lemma surrounding_revert_undoes_precompile_transfer :
    List.map (fun address => let result := run
      (call 241 address 3 0 0 0 (price address) ++ [96;0;96;0;253]) in
      (static_calls.Test.result_kind result, calls.Test.balance 42 result,
       calls.Test.balance address result)) [6;7] =
    List.repeat (Some InstructionResult.Revert, Some 10, Some 0) 2.
  Proof. vm_compute. reflexivity. Qed.
End Test.
