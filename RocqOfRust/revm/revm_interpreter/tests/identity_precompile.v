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
  Definition push2 (value : Z) : list Z :=
    [97; value / 256; value mod 256].

  Definition call (opcode address value input_size output_offset output_size gas : Z) :=
    push2 output_size ++ push2 output_offset ++ push2 input_size ++ [96; 0] ++
    (if (opcode =? 241) || (opcode =? 242) then [96; value] else []) ++
    [96; address] ++ push2 gas ++ [opcode].

  Definition initial (program : list Z) : CallFrame.state :=
    let state := calls.Test.initial program [] in
    {| InstructionContext.State.interpreter := InstructionContext.State.interpreter _ _ _ state;
       InstructionContext.State.host := StatefulHost.warm_account
         (InstructionContext.State.host _ _ _ state) 4 |}.

  Definition run (program : list Z) := CallRunner.run 300 (initial program).

  Definition memory_data : list Z :=
    [96; 171; 96; 0; 83; 96; 205; 96; 1; 83;
     96; 238; 96; 34; 83; 96; 255; 96; 35; 83].

  Definition output_memory result :=
    option_map (List.skipn 32) (calls.Test.memory_prefix 36 result).

  Lemma identity_copies_input_and_preserves_uncopied_output :
    let result := run (memory_data ++ call 241 4 0 2 32 4 18 ++ [0]) in
    (static_calls.Test.result_kind result, calls.Test.stack result,
     calls.Test.returned_bytes result, output_memory result,
     calls.Test.remaining_gas result) =
      (Some InstructionResult.Stop, Some [1], Some [171; 205],
       Some [171; 205; 238; 255], Some 99819).
  Proof. vm_compute. reflexivity. Qed.

  Lemma short_output_keeps_full_return_data :
    let result := run (memory_data ++ call 241 4 0 2 32 1 18 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result, output_memory result) =
      (Some [1], Some [171; 205], Some [171; 0; 238; 255]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_input_exact_gas_succeeds :
    let result := run (call 241 4 0 0 0 0 15 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result,
     calls.Test.remaining_gas result) = (Some [1], Some [], Some 99864).
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_input_insufficient_gas_fails :
    let result := run (call 241 4 0 0 0 0 14 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result,
     calls.Test.remaining_gas result) = (Some [0], Some [], Some 99865).
  Proof. vm_compute. reflexivity. Qed.

  Lemma gas_cost_rounds_input_to_words :
    List.map (fun size => calls.Test.stack
      (run (call 241 4 0 size 0 0 18 ++ [0]))) [1; 31; 32; 33] =
      [Some [1]; Some [1]; Some [1]; Some [0]] /\
    calls.Test.stack (run (call 241 4 0 33 0 0 21 ++ [0])) = Some [1].
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma failure_clears_prior_return_data_and_preserves_memory :
    let result := run (memory_data ++ call 241 4 0 2 32 4 18 ++
      call 241 4 0 2 32 4 17 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result, output_memory result) =
      (Some [0; 1], Some [], Some [171; 205; 238; 255]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma call_value_transfer_succeeds :
    let result := run (call 241 4 3 0 0 0 100 ++ [0]) in
    (calls.Test.stack result, calls.Test.balance 42 result, calls.Test.balance 4 result) =
      (Some [1], Some 7, Some 3).
  Proof. vm_compute. reflexivity. Qed.

  Lemma insufficient_balance_fails_before_identity :
    let result := run (call 241 4 11 0 0 0 100 ++ [0]) in
    (calls.Test.stack result, calls.Test.balance 42 result, calls.Test.balance 4 result) =
      (Some [0], Some 10, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma parent_revert_undoes_identity_transfer :
    let result := run (call 241 4 3 0 0 0 100 ++ [96; 0; 96; 0; 253]) in
    (static_calls.Test.result_kind result,
     calls.Test.balance 42 result, calls.Test.balance 4 result) =
      (Some InstructionResult.Revert, Some 10, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma identity_out_of_gas_undoes_value_transfer :
    let result := run (call 241 4 3 24577 0 0 0 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result,
     calls.Test.balance 42 result, calls.Test.balance 4 result) =
      (Some [0], Some [], Some 10, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma callcode_uses_bytecode_address_without_transferring_value :
    let result := run (memory_data ++ call 242 4 3 2 32 4 18 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result,
     calls.Test.balance 42 result, calls.Test.balance 4 result) =
      (Some [1], Some [171; 205], Some 10, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegatecall_uses_bytecode_address :
    let result := run (memory_data ++ call 244 4 0 2 32 4 18 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result,
     calls.Test.balance 42 result, calls.Test.balance 4 result) =
      (Some [1], Some [171; 205], Some 10, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma staticcall_can_execute_identity :
    let result := run (memory_data ++ call 250 4 0 2 32 4 18 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result, output_memory result) =
      (Some [1], Some [171; 205], Some [171; 205; 238; 255]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma identity_takes_precedence_over_account_code :
    let state := initial (call 241 4 0 0 0 0 15 ++ [0]) in
    let host := InstructionContext.State.host _ _ _ state in
    let result := CallRunner.run 100
      {| InstructionContext.State.interpreter := InstructionContext.State.interpreter _ _ _ state;
         InstructionContext.State.host := StatefulHost.with_accounts host
           (calls.Test.account 4 7 [254] :: host.(StatefulHost.accounts)) |} in
    (calls.Test.stack result, calls.Test.balance 4 result) = (Some [1], Some 7).
  Proof. vm_compute. reflexivity. Qed.

  Definition owned_inputs : CallInputs.t :=
    {| CallInputs.input := CallInput.Bytes
         (Impl_Bytes.copy_from_slice (List.map StatefulHost.rust_byte [171; 205]));
       CallInputs.return_memory_offset := {| Range.start := {| Integer.value := 0 |}; Range.end_ := {| Integer.value := 0 |} |};
       CallInputs.gas_limit := 18;
       CallInputs.bytecode_address := StatefulHost.rust_address 4;
       CallInputs.known_bytecode := None;
       CallInputs.target_address := StatefulHost.rust_address 4;
       CallInputs.caller := StatefulHost.rust_address 42;
       CallInputs.value := CallValue.Transfer (StatefulHost.rust_word 0);
       CallInputs.scheme := CallScheme.Call;
       CallInputs.is_static := false |}.

  Lemma identity_result_distinguishes_success_and_out_of_gas :
    let parent := InstructionContext.State.interpreter _ _ _ (initial [0]) in
    let success := PrecompileFrame.identity (CallFrame.child parent owned_inputs []) in
    let failure := PrecompileFrame.identity
      (CallFrame.child parent (owned_inputs <| CallInputs.gas_limit := 17 |>) []) in
    (success.(InterpreterResult.result),
     success.(InterpreterResult.gas).(Gas.remaining).(Integer.value),
     failure.(InterpreterResult.result),
     failure.(InterpreterResult.gas).(Gas.remaining).(Integer.value)) =
      (InstructionResult.Return, 0, InstructionResult.PrecompileOOG, 17).
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
             <| Gas.remaining := 99982 |> |>;
         InstructionContext.State.host := InstructionContext.State.host _ _ _ state |} in
    (calls.Test.stack result, calls.Test.returned_bytes result,
     calls.Test.remaining_gas result) = (Some [1], Some [171; 205], Some 99982).
  Proof. vm_compute. reflexivity. Qed.

  Lemma other_active_precompiles_remain_incomplete :
    List.map (fun address => calls.Test.stack
      (run (call 241 address 0 0 0 0 10000 ++ [0]))) [1; 5; 10; 17] =
      [None; None; None; None].
  Proof. vm_compute. reflexivity. Qed.

  Definition init_identity :=
    memory_data ++ call 241 4 0 2 32 2 18 ++ [80; 96; 2; 96; 32; 243].

  Lemma constructor_can_deploy_identity_output :
    let result := create.Test.run false init_identity 0 [0] in
    create.Test.code (create.Test.address false init_identity) result = Some [171; 205] /\
    create.Test.return_data result = Some [].
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma parent_revert_discards_identity_constructor :
    let result := create.Test.run false init_identity 0 [96; 0; 96; 0; 253] in
    create.Test.account (create.Test.address false init_identity) result = None /\
    create.Test.nonce 42 result = Some 7.
  Proof. vm_compute. split; reflexivity. Qed.
End Test.
