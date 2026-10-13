From Stdlib Require Import List ZArith.

Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import bytes.links.bytes.
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
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_precompile.tests.secp256k1.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition call (opcode value input_size output_offset output_size gas : Z) :=
    identity_precompile.Test.call opcode 1 value input_size output_offset output_size gas.

  Definition initial (program : list Z) : CallFrame.state :=
    let state := calls.Test.initial program [] in
    {| InstructionContext.State.interpreter := InstructionContext.State.interpreter _ _ _ state;
       InstructionContext.State.host := StatefulHost.warm_account
         (InstructionContext.State.host _ _ _ state) 1 |}.

  Definition run (program : list Z) := CallRunner.run 300 (initial program).

  Definition owned_inputs (data : list Z) (gas : Z) : CallInputs.t :=
    identity_precompile.Test.owned_inputs
      <| CallInputs.input := CallInput.Bytes
        (Impl_Bytes.copy_from_slice (List.map StatefulHost.rust_byte data)) |>
      <| CallInputs.gas_limit := {| Integer.value := gas |} |>
      <| CallInputs.bytecode_address := StatefulHost.rust_address 1 |>
      <| CallInputs.target_address := StatefulHost.rust_address 1 |>.

  Definition direct (data : list Z) (gas : Z) : InterpreterResult.t :=
    let parent := InstructionContext.State.interpreter _ _ _ (initial [0]) in
    PrecompileFrame.ecrecover (CallFrame.child parent (owned_inputs data gas) []).

  Definition direct_observation (result : InterpreterResult.t) :=
    (result.(InterpreterResult.result),
     result.(InterpreterResult.gas).(Gas.remaining).(Integer.value),
     List.map Integer.value result.(InterpreterResult.output)
       .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value)).

  Lemma valid_recovery_returns_padded_address_with_exact_cost :
    direct_observation (direct
      revm.revm_precompile.tests.secp256k1.Test.valid_key_input 3000) =
    (InstructionResult.Return, 0, revm.revm_precompile.tests.secp256k1.Test.valid_output).
  Proof. vm_compute. reflexivity. Qed.

  Lemma invalid_signature_is_return_with_empty_output :
    direct_observation (direct [] 5000) = (InstructionResult.Return, 2000, []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma invalid_signature_still_observes_gas_boundary :
    direct_observation (direct [] 2999) = (InstructionResult.PrecompileOOG, 2999, []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma out_of_gas_precedes_valid_signature_recovery :
    direct_observation (direct
      revm.revm_precompile.tests.secp256k1.Test.valid_key_input 2999) =
    (InstructionResult.PrecompileOOG, 2999, []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma invalid_recovery_reports_success_to_all_call_schemes :
    List.map (fun opcode =>
      let result := run (call opcode 0 0 0 0 3000 ++ [0]) in
      (calls.Test.stack result, calls.Test.returned_bytes result)) [241; 242; 244; 250] =
    List.repeat (Some [1], Some []) 4.
  Proof. vm_compute. reflexivity. Qed.

  Lemma insufficient_precompile_gas_reports_call_failure :
    let result := run (call 241 0 0 0 0 2999 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result) = (Some [0], Some []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma invalid_signature_success_preserves_value_transfer :
    let result := run (call 241 3 0 0 0 3000 ++ [0]) in
    (calls.Test.stack result, calls.Test.balance 42 result, calls.Test.balance 1 result) =
    (Some [1], Some 7, Some 3).
  Proof. vm_compute. reflexivity. Qed.

  Lemma gas_failure_reverts_value_transfer :
    let result := run (call 241 3 0 0 0 0 ++ [0]) in
    (calls.Test.stack result, calls.Test.balance 42 result, calls.Test.balance 1 result) =
    (Some [0], Some 10, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma recovery_precompile_takes_precedence_over_account_code :
    let state := initial (call 241 0 0 0 0 3000 ++ [0]) in
    let host := InstructionContext.State.host _ _ _ state in
    let result := CallRunner.run 100
      {| InstructionContext.State.interpreter := InstructionContext.State.interpreter _ _ _ state;
         InstructionContext.State.host := StatefulHost.with_accounts host
           (calls.Test.account 1 7 [254] :: host.(StatefulHost.accounts)) |} in
    (calls.Test.stack result, calls.Test.returned_bytes result, calls.Test.balance 1 result) =
    (Some [1], Some [], Some 7).
  Proof. vm_compute. reflexivity. Qed.

  Definition valid_memory : list Z :=
    List.concat (List.map (fun index =>
      [127] ++ List.firstn 32 (List.skipn (32 * index)%nat
        revm.revm_precompile.tests.secp256k1.Test.valid_key_input) ++
      [96; 32 * Z.of_nat index; 82]) (List.seq 0 4)).

  Lemma caller_receives_full_recovered_address :
    let result := run (valid_memory ++ call 241 0 128 128 32 3000 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result,
     option_map (List.skipn 128) (calls.Test.memory_prefix 160 result)) =
    (Some [1], Some revm.revm_precompile.tests.secp256k1.Test.valid_output,
      Some revm.revm_precompile.tests.secp256k1.Test.valid_output).
  Proof. vm_compute. reflexivity. Qed.

  Lemma invalid_second_recovery_clears_prior_return_data :
    let result := run (valid_memory ++ call 241 0 128 128 32 3000 ++
      call 241 0 0 0 0 3000 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result) = (Some [1; 1], Some []).
  Proof. vm_compute. reflexivity. Qed.
End Test.
