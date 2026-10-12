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
Require Import revm.revm_interpreter.tests.stateful_dispatch.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_interpreter.tests.static_calls.
Require Import revm.revm_precompile.simulate.modexp.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition call (opcode value input_size output_offset output_size gas : Z) :=
    identity_precompile.Test.call opcode 5 value input_size output_offset output_size gas.

  Definition initial (program : list Z) : CallFrame.state :=
    let state := calls.Test.initial program [] in
    {| InstructionContext.State.interpreter := InstructionContext.State.interpreter _ _ _ state;
       InstructionContext.State.host := StatefulHost.warm_account
         (InstructionContext.State.host _ _ _ state) 5 |}.

  Definition run (program : list Z) := CallRunner.run 300 (initial program).

  (** Encode base 2, exponent 5, and the two-byte modulus 13. *)
  Definition input : list Z :=
    List.repeat 0 31 ++ [1] ++ List.repeat 0 31 ++ [1] ++
    List.repeat 0 31 ++ [2] ++ [2; 5; 0; 13].
  Definition memory_data : list Z :=
    [96; 1; 96; 31; 83; 96; 1; 96; 63; 83;
     96; 2; 96; 95; 83; 96; 2; 96; 96; 83;
     96; 5; 96; 97; 83; 96; 13; 96; 99; 83].

  Lemma exact_minimum_gas_succeeds :
    let result := run (memory_data ++ call 241 0 100 128 2 200 ++ [0]) in
    (static_calls.Test.result_kind result, calls.Test.stack result,
     calls.Test.returned_bytes result) =
      (Some InstructionResult.Stop, Some [1], Some [0; 6]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma below_minimum_gas_fails :
    let result := run (memory_data ++ call 241 0 100 128 2 199 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result) = (Some [0], Some []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma all_call_schemes_execute_modexp :
    List.map (fun opcode => calls.Test.returned_bytes
      (run (memory_data ++ call opcode 0 100 128 2 200 ++ [0]))) [241; 242; 244; 250] =
      [Some [0; 6]; Some [0; 6]; Some [0; 6]; Some [0; 6]].
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_input_succeeds_with_empty_output :
    let result := run (call 241 0 0 0 0 200 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result,
     calls.Test.remaining_gas result) = (Some [1], Some [], Some 99679).
  Proof. vm_compute. reflexivity. Qed.

  Lemma missing_modulus_bytes_are_zero_padded :
    let result := run (memory_data ++ call 241 0 98 128 2 200 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result) = (Some [1], Some [0; 0]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma short_output_keeps_return_data_and_trailing_memory :
    let result := run (memory_data ++ [96; 238; 96; 129; 83] ++
      call 241 0 100 128 1 200 ++ [0]) in
    (calls.Test.returned_bytes result,
     option_map (List.skipn 128) (calls.Test.memory_prefix 130 result)) =
      (Some [0; 6], Some [0; 238]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma failed_call_clears_return_data_and_preserves_output_memory :
    let result := run (memory_data ++ call 241 0 100 128 2 200 ++
      call 241 0 100 128 2 199 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result,
     option_map (List.skipn 128) (calls.Test.memory_prefix 130 result)) =
      (Some [0; 1], Some [], Some [0; 6]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma successful_call_transfers_value :
    let result := run (call 241 3 0 0 0 200 ++ [0]) in
    (calls.Test.stack result, calls.Test.balance 42 result, calls.Test.balance 5 result) =
      (Some [1], Some 7, Some 3).
  Proof. vm_compute. reflexivity. Qed.

  Lemma insufficient_balance_fails_before_modexp :
    let result := run (call 241 11 0 0 0 200 ++ [0]) in
    (calls.Test.stack result, calls.Test.balance 42 result, calls.Test.balance 5 result) =
      (Some [0], Some 10, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma invalid_length_rolls_back_value_transfer :
    let result := run ([96; 1; 96; 0; 83] ++ call 241 3 32 0 0 200 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result,
     calls.Test.balance 42 result, calls.Test.balance 5 result) =
      (Some [0], Some [], Some 10, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma parent_revert_undoes_value_transfer :
    let result := run (call 241 3 0 0 0 200 ++ [96; 0; 96; 0; 253]) in
    (static_calls.Test.result_kind result, calls.Test.balance 42 result,
     calls.Test.balance 5 result) = (Some InstructionResult.Revert, Some 10, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma callcode_checks_funds_without_transferring_value :
    let result := run (memory_data ++ call 242 3 100 128 2 200 ++ [0]) in
    (calls.Test.stack result, calls.Test.returned_bytes result,
     calls.Test.balance 42 result, calls.Test.balance 5 result) =
      (Some [1], Some [0; 6], Some 10, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma modexp_takes_precedence_over_account_code :
    let state := initial (call 241 0 0 0 0 200 ++ [0]) in
    let host := InstructionContext.State.host _ _ _ state in
    let result := CallRunner.run 100
      {| InstructionContext.State.interpreter := InstructionContext.State.interpreter _ _ _ state;
         InstructionContext.State.host := StatefulHost.with_accounts host
           (calls.Test.account 5 7 [254] :: host.(StatefulHost.accounts)) |} in
    (calls.Test.stack result, calls.Test.returned_bytes result,
     calls.Test.balance 5 result) = (Some [1], Some [], Some 7).
  Proof. vm_compute. reflexivity. Qed.

  Definition owned_inputs := identity_precompile.Test.owned_inputs
    <| CallInputs.input := CallInput.Bytes
      (Impl_Bytes.copy_from_slice (List.map StatefulHost.rust_byte input)) |>
    <| CallInputs.gas_limit := 200 |>
    <| CallInputs.bytecode_address := StatefulHost.rust_address 5 |>
    <| CallInputs.target_address := StatefulHost.rust_address 5 |>.

  Definition frame_result_at (spec_id : SpecId.t) (input_bytes : list Z) (gas : Z) :=
    let parent := InstructionContext.State.interpreter _ _ _ (initial [0]) in
    let child := CallFrame.child parent
      (owned_inputs <| CallInputs.gas_limit := gas |>
        <| CallInputs.input := CallInput.Bytes
          (Impl_Bytes.copy_from_slice (List.map StatefulHost.rust_byte input_bytes)) |>) [] in
    PrecompileFrame.modexp (child
      <| @Interpreter.runtime_flag WIRE _ WIRE_types _ := child.(Interpreter.runtime_flag)
        <| RuntimeFlags.spec_id := spec_id |> |>).

  Definition frame_result := frame_result_at SpecId.CANCUN.

  Lemma native_status_and_gas_on_success_and_failures :
    List.map (fun result => (result.(InterpreterResult.result),
      result.(InterpreterResult.gas).(Gas.remaining).(Integer.value)))
      [frame_result input 200; frame_result input 199; frame_result [1] 200] =
      [(InstructionResult.Return, 0); (InstructionResult.PrecompileOOG, 199);
       (InstructionResult.PrecompileError, 200)].
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
             <| Gas.remaining := 99800 |> |>;
         InstructionContext.State.host := InstructionContext.State.host _ _ _ state |} in
    (calls.Test.stack result, calls.Test.returned_bytes result,
     calls.Test.remaining_gas result) = (Some [1], Some [0; 6], Some 99800).
  Proof. vm_compute. reflexivity. Qed.

  Definition init_modexp :=
    memory_data ++ call 241 0 100 128 2 200 ++ [80; 96; 2; 96; 128; 243].

  Lemma constructor_can_deploy_result :
    let result := create.Test.run false init_modexp 0 [0] in
    create.Test.code (create.Test.address false init_modexp) result = Some [0; 6] /\
    create.Test.return_data result = Some [].
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma parent_revert_discards_modexp_constructor :
    let result := create.Test.run false init_modexp 0 [96; 0; 96; 0; 253] in
    create.Test.account (create.Test.address false init_modexp) result = None /\
    create.Test.nonce 42 result = Some 7.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma frame_selects_osaka_pricing :
    List.map (fun spec_id =>
      let result := frame_result_at spec_id input 500 in
      (result.(InterpreterResult.result),
       result.(InterpreterResult.gas).(Gas.remaining).(Integer.value)))
      [SpecId.CANCUN; SpecId.PRAGUE; SpecId.OSAKA] =
      [(InstructionResult.Return, 300); (InstructionResult.Return, 300);
       (InstructionResult.Return, 0)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma osaka_frame_gas_and_length_error_precedence :
    List.map (fun result => (result.(InterpreterResult.result),
      result.(InterpreterResult.gas).(Gas.remaining).(Integer.value)))
      [frame_result_at SpecId.OSAKA input 499;
       frame_result_at SpecId.OSAKA [1] 499;
       frame_result_at SpecId.OSAKA [1] 500;
       frame_result_at SpecId.OSAKA (Modexp.Test.header 0 1025 0) 500] =
      [(InstructionResult.PrecompileOOG, 499); (InstructionResult.PrecompileOOG, 499);
       (InstructionResult.PrecompileError, 500); (InstructionResult.PrecompileError, 500)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma osaka_frame_preserves_modulus_sized_output :
    let result := frame_result_at SpecId.OSAKA input 500 in
    List.map Integer.value result.(InterpreterResult.output)
      .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value) = [0; 6].
  Proof. vm_compute. reflexivity. Qed.

  Definition run_osaka (program : list Z) :=
    let state := initial program in
    let interpreter := InstructionContext.State.interpreter _ _ _ state in
    CallRunner.run 300
      {| InstructionContext.State.interpreter := interpreter
           <| @Interpreter.runtime_flag WIRE _ WIRE_types _ := interpreter.(Interpreter.runtime_flag)
             <| RuntimeFlags.spec_id := SpecId.OSAKA |> |>;
         InstructionContext.State.host := InstructionContext.State.host _ _ _ state |}.

  Lemma public_runner_executes_osaka :
    static_calls.Test.result_kind (run_osaka [0]) = Some InstructionResult.Stop.
  Proof. vm_compute. reflexivity. Qed.

  Lemma public_runner_uses_osaka_modexp_minimum :
    let enough := run_osaka (memory_data ++ call 241 0 100 128 2 500 ++ [0]) in
    let short := run_osaka (memory_data ++ call 241 0 100 128 2 499 ++ [0]) in
    (calls.Test.stack enough, calls.Test.returned_bytes enough,
     calls.Test.stack short, calls.Test.returned_bytes short) =
    (Some [1], Some [0; 6], Some [0], Some []).
  Proof. vm_compute. reflexivity. Qed.
  Lemma modexp_is_not_a_precompile_before_byzantium :
    PrecompileFrame.enabled SpecId.SPURIOUS_DRAGON 5 = false /\
    PrecompileFrame.enabled SpecId.BYZANTIUM 5 = true.
  Proof. vm_compute. auto. Qed.

  Lemma inactive_modexp_is_not_executed :
    let child := interpreter_with_spec_id
      (InstructionContext.State.interpreter _ _ _ (initial [0])) SpecId.SPURIOUS_DRAGON in
    PrecompileFrame.run 5 child = None.
  Proof. reflexivity. Qed.

  (** Exercise the frame engine directly while the public gate for older forks
      remains closed. Address 5 must execute account code before Byzantium. *)
  Definition address_five_call (spec : SpecId.t) :=
    let state := initial (calls.Test.call_to 5 0 0 0 50000 ++ [0]) in
    let interpreter := interpreter_with_spec_id
      (InstructionContext.State.interpreter _ _ _ state) spec in
    let host := (InstructionContext.State.host _ _ _ state)
      <| StatefulHost.spec_id := spec |> in
    let host := StatefulHost.with_accounts host
      (StatefulHost.update_account 5
        (fun account => account <| StatefulHost.Account.code := [96; 7; 96; 0; 85; 0] |>)
        host.(StatefulHost.accounts)) in
    CallRunner.execute 100 host []
      {| InstructionContext.State.interpreter := interpreter;
         InstructionContext.State.host := host |}.

  Lemma address_five_executes_account_code_before_byzantium :
    calls.Test.storage 5 (address_five_call SpecId.SPURIOUS_DRAGON) = Some [(0, 7)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma address_five_bypasses_account_code_from_byzantium :
    calls.Test.storage 5 (address_five_call SpecId.BYZANTIUM) = Some [].
  Proof. vm_compute. reflexivity. Qed.

End Test.
