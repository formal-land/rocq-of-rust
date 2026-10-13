From Stdlib Require Import List ZArith.

Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.simulate.dispatch.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.simulate.step.
Require Import revm.revm_interpreter.tests.call_frame.
Require Import revm.revm_interpreter.tests.call_runner.
Require Import revm.revm_interpreter.tests.calls.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.tests.stateful_dispatch.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition input : StatefulHost.Input.t :=
    add11_input
      <| StatefulHost.Input.block := add11_input.(StatefulHost.Input.block)
        <| StatefulHost.Environment.Block.number := 300 |>
        <| StatefulHost.Environment.Block.hashes := [(44, 444); (299, 999)] |> |>
      <| StatefulHost.Input.transaction := add11_input.(StatefulHost.Input.transaction)
        <| StatefulHost.Environment.Transaction.gas_price := 123 |>
        <| StatefulHost.Environment.Transaction.blob_hashes := [456; 789] |> |>
      <| StatefulHost.Input.call := {| StatefulHost.Environment.Call.caller := 77 |} |>.

  Definition initial (spec : SpecId.t) (gas_limit : Z) (code args : list Z) :
      CallFrame.state :=
    let interpreter := interpreter_with_spec_id
      (make_interpreter_with_bytecode (List.map StatefulHost.rust_byte code)
        {| Stack.value := List.map StatefulHost.rust_word args |}) spec in
    {| InstructionContext.State.interpreter := interpreter
         <| @Interpreter.gas WIRE _ WIRE_types _ := interpreter.(Interpreter.gas)
           <| Gas.limit := {| Integer.value := gas_limit |} |>
           <| Gas.remaining := {| Integer.value := gas_limit |} |> |>;
       InstructionContext.State.host := StatefulHost.make input |}.

  Definition observe (state : CallFrame.state) :=
    let interpreter := InstructionContext.State.interpreter _ _ _ state in
    (List.map Uint.value interpreter.(Interpreter.stack).(Stack.value),
     interpreter.(Interpreter.gas).(Gas.remaining).(Integer.value),
     match interpreter.(Interpreter.bytecode).(Bytecode.action) with
     | Some (InterpreterAction.Return output) => Some output.(InterpreterResult.result)
     | _ => None
     end).

  Definition step (spec : SpecId.t) (gas_limit opcode : Z) (args : list Z) :=
    let state := initial spec gas_limit [opcode] args in
    match InterpreterDispatch.step_result_stateful InterpreterTypes.I CallRunner.table state with
    | InterpreterStep.Result.Success state
    | InterpreterStep.Result.OutOfGas state => Some (observe state)
    | InterpreterStep.Result.MissingInstruction => None
    end.

  Definition run (spec : SpecId.t) (gas_limit : Z) (code args : list Z) :=
    CallRunner.run 100 (initial spec gas_limit code args).

  Definition status (result : option (InterpreterAction.t * CallFrame.state)) :=
    match result with
    | Some (InterpreterAction.Return output, _) => Some output.(InterpreterResult.result)
    | _ => None
    end.

  Lemma origin_reads_transaction_sender_with_exact_gas :
    step SpecId.CANCUN 2 50 [] = Some ([77], 0, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma gasprice_reads_effective_price_with_exact_gas :
    step SpecId.PRAGUE 2 58 [] = Some ([123], 0, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma environment_pushes_require_static_gas :
    List.map (fun opcode => step SpecId.CANCUN 1 opcode []) [50; 58] =
    [Some ([], 0, Some InstructionResult.OutOfGas);
     Some ([], 0, Some InstructionResult.OutOfGas)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma missing_state_test_blockhash_matches_geth :
    StatefulHost.state_test_block_hash 0 =
      0x044852b2a670ade5407e78fb2863c51de9fcb96542a07186fe3aeda6bb8a116d.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blockhash_oldest_available_block :
    step SpecId.CANCUN 20 64 [44] = Some ([444], 0, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blockhash_previous_block :
    step SpecId.PRAGUE 20 64 [299] = Some ([999], 0, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blockhash_outside_recent_range_returns_zero :
    List.map (fun number => step SpecId.CANCUN 20 64 [number])
      [43; 300; 301; 2 ^ 256 - 1] =
    List.repeat (Some ([0], 0, None)) 4.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blockhash_underflow_charges_static_gas :
    step SpecId.CANCUN 100 64 [] =
    Some ([], 80, Some InstructionResult.StackUnderflow).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blockhash_insufficient_gas_precedes_stack_check :
    step SpecId.CANCUN 19 64 [] =
    Some ([], 0, Some InstructionResult.OutOfGas).
  Proof. vm_compute. reflexivity. Qed.

  Lemma missing_recent_blockhash_is_external_error :
    step SpecId.CANCUN 20 64 [298] =
    Some ([298], 0, Some InstructionResult.FatalExternalError).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blobhash_indexes_transaction_hashes_with_exact_gas :
    List.map (fun index => step SpecId.CANCUN 3 73 [index]) [0; 1] =
    [Some ([456], 0, None); Some ([789], 0, None)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma blobhash_outside_transaction_list_returns_zero :
    List.map (fun index => step SpecId.PRAGUE 3 73 [index]) [2; 2 ^ 256 - 1] =
    [Some ([0], 0, None); Some ([0], 0, None)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma blobhash_underflow_charges_static_gas :
    step SpecId.CANCUN 100 73 [] =
    Some ([], 97, Some InstructionResult.StackUnderflow).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blobhash_rejects_before_cancun :
    step SpecId.SHANGHAI 100 73 [] =
    Some ([], 97, Some InstructionResult.NotActivated).
  Proof. vm_compute. reflexivity. Qed.

  Lemma invalid_has_its_own_halt_status :
    step SpecId.CANCUN 0 254 [] =
    Some ([], 0, Some InstructionResult.InvalidFEOpcode).
  Proof. vm_compute. reflexivity. Qed.

  Lemma public_runner_executes_origin_and_gasprice :
    (calls.Test.stack (run SpecId.CANCUN 100 [50; 58; 0] []),
     calls.Test.remaining_gas (run SpecId.CANCUN 100 [50; 58; 0] []),
     status (run SpecId.CANCUN 100 [50; 58; 0] [])) =
    (Some [123; 77], Some 96, Some InstructionResult.Stop).
  Proof. vm_compute. reflexivity. Qed.

  Lemma public_runner_executes_blockhash_and_blobhash :
    (calls.Test.stack (run SpecId.PRAGUE 25 [64; 80; 73; 0] [299; 1]),
     calls.Test.remaining_gas (run SpecId.PRAGUE 25 [64; 80; 73; 0] [299; 1]),
     status (run SpecId.PRAGUE 25 [64; 80; 73; 0] [299; 1])) =
    (Some [789], Some 0, Some InstructionResult.Stop).
  Proof. vm_compute. reflexivity. Qed.

  Lemma public_runner_preserves_missing_host_data_as_incomplete :
    run SpecId.CANCUN 100 [64; 0] [298] = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma public_runner_invalid_is_complete_exception :
    status (run SpecId.CANCUN 100 [254] []) = Some InstructionResult.InvalidFEOpcode.
  Proof. vm_compute. reflexivity. Qed.

  Lemma public_runner_undefined_opcode_is_complete_exception :
    status (run SpecId.CANCUN 100 [12] []) = Some InstructionResult.OpcodeNotFound.
  Proof. vm_compute. reflexivity. Qed.

  Definition mcopy_program : list Z :=
    [96; 42; 95; 83; 96; 1; 95; 96; 1; 94; 0].

  Lemma public_runner_executes_mcopy :
    (calls.Test.memory_prefix 2 (run SpecId.CANCUN 100 mcopy_program []),
     calls.Test.remaining_gas (run SpecId.CANCUN 100 mcopy_program []),
     status (run SpecId.CANCUN 100 mcopy_program [])) =
    (Some [42; 42], Some 75, Some InstructionResult.Stop).
  Proof. vm_compute. reflexivity. Qed.

  Definition nested_initial (parent child : list Z) : CallFrame.state :=
    let state := calls.Test.initial parent child in
    let host := InstructionContext.State.host _ _ _ state in
    {| InstructionContext.State.interpreter := InstructionContext.State.interpreter _ _ _ state;
       InstructionContext.State.host := host
         <| StatefulHost.input := host.(StatefulHost.input)
           <| StatefulHost.Input.call := {| StatefulHost.Environment.Call.caller := 77 |} |> |> |}.

  Definition nested_run (parent child : list Z) :=
    CallRunner.run 300 (nested_initial parent child).

  Definition slot (address key : Z) (result : option (InterpreterAction.t * CallFrame.state)) :=
    option_map (StatefulHost.lookup_word key) (calls.Test.storage address result).

  Lemma child_origin_preserves_transaction_sender :
    slot 43 0 (nested_run (calls.Test.call 0 0 0 50000 ++ [0])
      [50; 95; 85; 51; 96; 1; 85; 0]) = Some 77.
  Proof. vm_compute. reflexivity. Qed.

  Lemma child_caller_remains_parent_contract :
    slot 43 1 (nested_run (calls.Test.call 0 0 0 50000 ++ [0])
      [50; 95; 85; 51; 96; 1; 85; 0]) = Some 42.
  Proof. vm_compute. reflexivity. Qed.

  Lemma invalid_child_returns_failure_and_rolls_back_storage :
    let result := nested_run (calls.Test.call 0 0 0 50000 ++ [0])
      (calls.Test.write_seven ++ [254]) in
    (calls.Test.stack result, calls.Test.storage 43 result, status result) =
    (Some [0], Some [], Some InstructionResult.Stop).
  Proof. vm_compute. reflexivity. Qed.

  Lemma invalid_child_rolls_back_value_transfer_and_consumes_child_gas :
    let result := nested_run (calls.Test.call 3 0 0 50000 ++ [0]) [254] in
    (calls.Test.balance 42 result, calls.Test.balance 43 result,
     calls.Test.remaining_gas result) = (Some 10, Some 0, Some 38379).
  Proof. vm_compute. reflexivity. Qed.

  Lemma jump_rejects_maximal_usize_before_unary_conversion :
    step SpecId.CANCUN 100 86 [2 ^ 64 - 1] =
    Some ([], 92, Some InstructionResult.InvalidJump).
  Proof. vm_compute. reflexivity. Qed.

  Lemma taken_jumpi_rejects_maximal_usize_before_unary_conversion :
    step SpecId.PRAGUE 100 87 [2 ^ 64 - 1; 1] =
    Some ([], 90, Some InstructionResult.InvalidJump).
  Proof. vm_compute. reflexivity. Qed.

  Lemma untaken_jumpi_ignores_maximal_target :
    step SpecId.CANCUN 100 87 [2 ^ 256 - 1; 0; 17] =
    Some ([17], 90, None).
  Proof. vm_compute. reflexivity. Qed.

  Definition push_maximal_usize : list Z :=
    [103; 255; 255; 255; 255; 255; 255; 255; 255].

  Lemma public_runner_huge_jump_is_complete_invalid_jump :
    status (run SpecId.CANCUN 100 (push_maximal_usize ++ [86]) []) =
    Some InstructionResult.InvalidJump.
  Proof. vm_compute. reflexivity. Qed.

  Lemma public_runner_taken_huge_jumpi_is_complete_invalid_jump :
    status (run SpecId.PRAGUE 100 ([96; 1] ++ push_maximal_usize ++ [87]) []) =
    Some InstructionResult.InvalidJump.
  Proof. vm_compute. reflexivity. Qed.

  Lemma public_runner_untaken_huge_jumpi_reaches_stop :
    let result := run SpecId.CANCUN 100 ([95] ++ push_maximal_usize ++ [87; 0]) [] in
    (status result, calls.Test.stack result, calls.Test.remaining_gas result) =
    (Some InstructionResult.Stop, Some [], Some 85).
  Proof. vm_compute. reflexivity. Qed.

  Lemma public_runner_keeps_valid_jumpdest :
    let result := run SpecId.CANCUN 100 [86; 91; 0] [1] in
    (status result, calls.Test.remaining_gas result) =
    (Some InstructionResult.Stop, Some 91).
  Proof. vm_compute. reflexivity. Qed.

  Lemma jumpdest_in_push_data_remains_invalid :
    status (run SpecId.CANCUN 100 [86; 96; 91; 0] [2]) =
    Some InstructionResult.InvalidJump.
  Proof. vm_compute. reflexivity. Qed.

  Definition byte_values : list Z := List.map Z.of_nat (List.seq 0 256).

  Definition undefined_bytes : list Z :=
    List.filter CallRunner.undefined_legacy_opcode byte_values.

  Lemma legacy_opcode_classification_covers_every_byte_once :
    List.forallb (fun opcode =>
      (CallRunner.supported_opcode opcode || CallRunner.undefined_legacy_opcode opcode) &&
      negb (CallRunner.supported_opcode opcode && CallRunner.undefined_legacy_opcode opcode))
      byte_values = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma malformed_bytes_remain_outside_opcode_classification :
    List.map (fun opcode =>
      CallRunner.supported_opcode opcode || CallRunner.undefined_legacy_opcode opcode)
      [-1; 256; 2 ^ 256] = [false; false; false].
  Proof. vm_compute. reflexivity. Qed.

  Lemma every_undefined_legacy_byte_reports_opcode_not_found :
    List.map (fun opcode => status (run SpecId.CANCUN 0 [opcode] [])) undefined_bytes =
    List.repeat (Some InstructionResult.OpcodeNotFound) (List.length undefined_bytes).
  Proof. vm_compute. reflexivity. Qed.

  Lemma undefined_handler_has_no_stack_requirement_or_static_gas :
    step SpecId.PRAGUE 100 12 [17] =
    Some ([17], 100, Some InstructionResult.OpcodeNotFound).
  Proof. vm_compute. reflexivity. Qed.

  Lemma clz_remains_known_but_not_activated_before_osaka :
    status (run SpecId.PRAGUE 100 [30] []) = Some InstructionResult.NotActivated.
  Proof. vm_compute. reflexivity. Qed.

  Lemma undefined_child_rolls_back_writes_and_consumes_child_budget :
    let result := nested_run (calls.Test.call 0 0 0 50000 ++ [0])
      (calls.Test.write_seven ++ [12]) in
    (calls.Test.stack result, calls.Test.storage 43 result,
     calls.Test.remaining_gas result, status result) =
    (Some [0], Some [], Some 47379, Some InstructionResult.Stop).
  Proof. vm_compute. reflexivity. Qed.

  Lemma pairing_precompile_is_supported :
    calls.Test.stack (nested_run (calls.Test.call_to 8 0 0 0 50000 ++ [0]) []) =
      Some [1].
  Proof. vm_compute. reflexivity. Qed.

  Lemma public_osaka_clz_has_exact_gas_and_result :
    let result := run SpecId.OSAKA 5 [30; 0] [0] in
    (status result, calls.Test.stack result, calls.Test.remaining_gas result) =
    (Some InstructionResult.Stop, Some [256], Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma public_osaka_clz_underflow :
    status (run SpecId.OSAKA 5 [30] []) = Some InstructionResult.StackUnderflow.
  Proof. vm_compute. reflexivity. Qed.

  Lemma public_osaka_create_keeps_initcode_limit :
    status (run SpecId.OSAKA 50000 [98; 0; 192; 1; 95; 95; 240] []) =
    Some InstructionResult.CreateInitCodeSizeLimit.
  Proof. vm_compute. reflexivity. Qed.

  Definition p256_call : list Z :=
    [95; 95; 95; 95; 95; 97; 1; 0; 97; 195; 80; 241; 0].

  Lemma public_osaka_p256_is_explicitly_unsupported :
    List.map (fun spec => status (run spec 100000 p256_call []))
      [SpecId.PRAGUE; SpecId.OSAKA; SpecId.AMSTERDAM] =
    [Some InstructionResult.Stop; None; None].
  Proof. vm_compute. reflexivity. Qed.
End Test.
