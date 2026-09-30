From Stdlib Require Import List ZArith.

Require Import alloc.links.boxed.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import bytes.links.bytes.
Require Import core.ops.links.range.
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
Require Import revm.revm_interpreter.tests.create.
Require Import revm.revm_interpreter.tests.identity_precompile.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.tests.precompile_frame.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_interpreter.tests.static_calls.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition empty_digest : list Z := [227; 176; 196; 66; 152; 252; 28; 20; 154; 251; 244; 200; 153; 111; 185; 36; 39; 174; 65; 228; 100; 155; 147; 76; 164; 149; 153; 27; 120; 82; 184; 85].
  Definition input_digest : list Z := [18; 61; 76; 126; 242; 209; 96; 10; 27; 58; 15; 106; 221; 198; 10; 16; 240; 90; 52; 149; 201; 64; 159; 46; 203; 244; 204; 9; 93; 0; 10; 107].

  Definition call (opcode value input_size output_offset output_size gas : Z) :=
    identity_precompile.Test.call opcode 2 value input_size output_offset output_size gas.

  Definition initial (program : list Z) : CallFrame.state :=
    let state := calls.Test.initial program [] in
    {| InstructionContext.State.interpreter := InstructionContext.State.interpreter _ _ _ state;
       InstructionContext.State.host := StatefulHost.warm_account
         (InstructionContext.State.host _ _ _ state) 2 |}.

  Definition run (program : list Z) := CallRunner.run 300 (initial program).
  Definition memory_data := identity_precompile.Test.memory_data.
  Definition output_memory := identity_precompile.Test.output_memory.

  Lemma empty_input_returns_digest_with_exact_gas :
    let result := run (call 241 0 0 0 0 60 ++ [0]) in
    (static_calls.Test.result_kind result, calls.Test.stack result,
     calls.Test.returned_bytes result, calls.Test.remaining_gas result) =
      (Some InstructionResult.Stop, Some [1], Some empty_digest, Some 99819).
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_input_insufficient_gas_fails :
    let result := run (call 241 0 0 0 0 59 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result,
     calls.Test.remaining_gas result) = (Some [0], Some [], Some 99820).
  Proof. vm_compute. reflexivity. Qed.

  Lemma short_output_keeps_full_digest_and_trailing_memory :
    let result := run (memory_data ++ call 241 0 2 32 2 72 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result, output_memory result,
     calls.Test.remaining_gas result) =
      (Some [1], Some input_digest, Some (List.firstn 2 input_digest ++ [238; 255]),
       Some 99765).
  Proof. vm_compute. reflexivity. Qed.

  Lemma all_call_schemes_execute_sha256 :
    List.map (fun opcode => calls.Test.returned_bytes
      (run (memory_data ++ call opcode 0 2 32 32 72 ++ [0]))) [241; 242; 244; 250] =
      [Some input_digest; Some input_digest; Some input_digest; Some input_digest].
  Proof. vm_compute. reflexivity. Qed.

  Lemma gas_cost_rounds_input_to_words :
    List.map (fun size => calls.Test.stack
      (run (call 241 0 size 0 0 72 ++ [0]))) [1; 31; 32; 33] =
      [Some [1]; Some [1]; Some [1]; Some [0]] /\
    calls.Test.stack (run (call 241 0 33 0 0 84 ++ [0])) = Some [1].
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma failed_call_clears_return_data_and_preserves_output_memory :
    let result := run (memory_data ++ call 241 0 2 32 2 72 ++
      call 241 0 2 32 2 71 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result, output_memory result) =
      (Some [0; 1], Some [], Some (List.firstn 2 input_digest ++ [238; 255])).
  Proof. vm_compute. reflexivity. Qed.

  Lemma successful_call_transfers_value :
    let result := run (call 241 3 0 0 0 60 ++ [0]) in
    (calls.Test.stack result, calls.Test.balance 42 result, calls.Test.balance 2 result) =
      (Some [1], Some 7, Some 3).
  Proof. vm_compute. reflexivity. Qed.

  Lemma insufficient_balance_fails_before_hashing :
    let result := run (call 241 11 0 0 0 60 ++ [0]) in
    (calls.Test.stack result, calls.Test.balance 42 result, calls.Test.balance 2 result) =
      (Some [0], Some 10, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma out_of_gas_rolls_back_value_transfer :
    let result := run (call 241 3 5985 0 0 0 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result,
     calls.Test.balance 42 result, calls.Test.balance 2 result) =
      (Some [0], Some [], Some 10, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma parent_revert_undoes_value_transfer :
    let result := run (call 241 3 0 0 0 60 ++ [96; 0; 96; 0; 253]) in
    (static_calls.Test.result_kind result, calls.Test.balance 42 result,
     calls.Test.balance 2 result) = (Some InstructionResult.Revert, Some 10, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma callcode_checks_funds_without_transferring_value :
    let result := run (memory_data ++ call 242 3 2 32 2 72 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result,
     calls.Test.balance 42 result, calls.Test.balance 2 result) =
      (Some [1], Some input_digest, Some 10, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma sha256_takes_precedence_over_account_code :
    let state := initial (call 241 0 0 0 0 60 ++ [0]) in
    let host := InstructionContext.State.host _ _ _ state in
    let result := CallRunner.run 100
      {| InstructionContext.State.interpreter := InstructionContext.State.interpreter _ _ _ state;
         InstructionContext.State.host := StatefulHost.with_accounts host
           (calls.Test.account 2 7 [254] :: host.(StatefulHost.accounts)) |} in
    (calls.Test.stack result, calls.Test.returned_bytes result,
     calls.Test.balance 2 result) = (Some [1], Some empty_digest, Some 7).
  Proof. vm_compute. reflexivity. Qed.

  Definition owned_inputs := identity_precompile.Test.owned_inputs
    <| CallInputs.gas_limit := 72 |>
    <| CallInputs.bytecode_address := StatefulHost.rust_address 2 |>
    <| CallInputs.target_address := StatefulHost.rust_address 2 |>.

  Lemma native_status_and_gas_on_success_and_failure :
    let parent := InstructionContext.State.interpreter _ _ _ (initial [0]) in
    let success := PrecompileFrame.sha256 (CallFrame.child parent owned_inputs []) in
    let failure := PrecompileFrame.sha256
      (CallFrame.child parent (owned_inputs <| CallInputs.gas_limit := 71 |>) []) in
    (success.(InterpreterResult.result),
     success.(InterpreterResult.gas).(Gas.remaining).(Integer.value),
     failure.(InterpreterResult.result),
     failure.(InterpreterResult.gas).(Gas.remaining).(Integer.value)) =
      (InstructionResult.Return, 0, InstructionResult.PrecompileOOG, 71).
  Proof. vm_compute. reflexivity. Qed.

  Lemma owned_input_does_not_require_known_bytecode :
    let state := initial [0] in
    let interpreter := InstructionContext.State.interpreter _ _ _ state in
    let result := CallRunner.run 10
      {| InstructionContext.State.interpreter := interpreter
           <| @Interpreter.bytecode WIRE _ WIRE_types _ := interpreter.(Interpreter.bytecode)
             <| Bytecode.action := Some (InterpreterAction.NewFrame
               (FrameInput.Call {| Box.value := owned_inputs |})) |> |>
           <| @Interpreter.gas WIRE _ WIRE_types _ := interpreter.(Interpreter.gas)
             <| Gas.remaining := 99928 |> |>;
         InstructionContext.State.host := InstructionContext.State.host _ _ _ state |} in
    (calls.Test.stack result, calls.Test.returned_bytes result,
     calls.Test.remaining_gas result) = (Some [1], Some input_digest, Some 99928).
  Proof. vm_compute. reflexivity. Qed.

  Definition init_sha256 :=
    memory_data ++ call 241 0 2 32 32 72 ++ [80; 96; 32; 96; 32; 243].

  Lemma constructor_can_deploy_digest :
    let result := create.Test.run false init_sha256 0 [0] in
    create.Test.code (create.Test.address false init_sha256) result = Some input_digest /\
    create.Test.return_data result = Some [].
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma parent_revert_discards_sha256_constructor :
    let result := create.Test.run false init_sha256 0 [96; 0; 96; 0; 253] in
    create.Test.account (create.Test.address false init_sha256) result = None /\
    create.Test.nonce 42 result = Some 7.
  Proof. vm_compute. split; reflexivity. Qed.
End Test.
