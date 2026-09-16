From Stdlib Require Import List ZArith.

Require Import alloy_primitives.bytes.links.mod.
Require Import bytes.links.bytes.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.call_frame.
Require Import revm.revm_interpreter.tests.call_runner.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.tests.stateful_dispatch.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition account (address balance : Z) (code : list Z) :=
    add11_account <| StatefulHost.Account.address := address |>
      <| StatefulHost.Account.balance := balance |>
      <| StatefulHost.Account.code := code |>.

  Definition initial (parent child : list Z) : CallFrame.state :=
    let host := StatefulHost.make
      (add11_input <| StatefulHost.Input.state :=
        [account 42 10 parent; account 43 0 child;
         account 44 0 [96; 9; 96; 0; 85; 0]] |>) in
    let interpreter := make_interpreter_with_bytecode
      (List.map StatefulHost.rust_byte parent) {| Stack.value := [] |} in
    let interpreter := interpreter
      <| @Interpreter.input WIRE _ WIRE_types _ :=
        empty_input <| Input.target_address := StatefulHost.rust_address 42 |> |>
      <| @Interpreter.gas WIRE _ WIRE_types _ :=
        interpreter.(Interpreter.gas) <| Gas.limit := 100000 |> <| Gas.remaining := 100000 |> |> in
    {| InstructionContext.State.interpreter := interpreter;
       InstructionContext.State.host := StatefulHost.warm_account host 42 |}.

  Definition call_to (address value in_size out_size gas : Z) : list Z :=
    [96; out_size; 96; 0; 96; in_size; 96; 0; 96; value; 96; address;
     97; Z.div gas 256; Z.modulo gas 256; 241].

  Definition call := call_to 43.

  Definition write_seven : list Z := [96; 7; 96; 0; 85].
  Definition store_result : list Z := [96; 0; 85; 0].

  Definition run (parent child : list Z) := CallRunner.run 200 (initial parent child).

  Definition storage (address : Z) (result : option (InterpreterAction.t * CallFrame.state)) :=
    match result with
    | Some (_, state) => option_map StatefulHost.Account.storage
        (StatefulHost.find_account address
          (InstructionContext.State.host _ _ _ state).(StatefulHost.accounts))
    | None => None
    end.

  Definition stack (result : option (InterpreterAction.t * CallFrame.state)) :=
    match result with
    | Some (_, state) => Some (List.map Uint.value
        (InstructionContext.State.interpreter _ _ _ state)
          .(Interpreter.stack).(Stack.value))
    | None => None
    end.

  Definition balance (address : Z) (result : option (InterpreterAction.t * CallFrame.state)) :=
    match result with
    | Some (_, state) => Some (CallFrame.balance
        (InstructionContext.State.host _ _ _ state) address)
    | None => None
    end.

  Lemma successful_child_keeps_storage :
    storage 43 (run (call 0 0 0 50000 ++ store_result) (write_seven ++ [0])) = Some [(0, 7)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma caller_continues_and_stores_success :
    storage 42 (run (call 0 0 0 50000 ++ store_result) (write_seven ++ [0])) = Some [(0, 1)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma child_revert_undoes_storage :
    storage 43 (run (call 0 0 0 50000 ++ [0])
      (write_seven ++ [96; 0; 96; 0; 253])) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma child_revert_returns_failure_to_caller :
    stack (run (call 0 0 0 50000 ++ [0])
      (write_seven ++ [96; 0; 96; 0; 253])) = Some [0].
  Proof. vm_compute. reflexivity. Qed.

  Lemma parent_revert_undoes_successful_child :
    storage 43 (run (call 0 0 0 50000 ++ [96; 0; 96; 0; 253])
      (write_seven ++ [0])) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma child_underflow_undoes_write :
    storage 43 (run (call 0 0 0 50000 ++ [0]) (write_seven ++ [80])) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma child_out_of_gas_returns_failure :
    stack (run (call 0 0 0 50 ++ [0]) (write_seven ++ [0])) = Some [0].
  Proof. vm_compute. reflexivity. Qed.

  Lemma successful_value_transfer :
    balance 43 (run (call 3 0 0 50000 ++ [0]) [0]) = Some 3.
  Proof. vm_compute. reflexivity. Qed.

  Lemma successful_value_transfer_debits_caller :
    balance 42 (run (call 3 0 0 50000 ++ [0]) [0]) = Some 7.
  Proof. vm_compute. reflexivity. Qed.

  Lemma revert_undoes_value_transfer :
    balance 42 (run (call 3 0 0 50000 ++ [0]) [96; 0; 96; 0; 253]) = Some 10.
  Proof. vm_compute. reflexivity. Qed.

  Lemma insufficient_balance_returns_failure :
    stack (run (call 11 0 0 50000 ++ [0]) [0]) = Some [0].
  Proof. vm_compute. reflexivity. Qed.

  Lemma insufficient_balance_does_not_run_child :
    storage 43 (run (call 11 0 0 50000 ++ [0]) (write_seven ++ [0])) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_code_call_succeeds :
    stack (run (call 0 0 0 50000 ++ [0]) []) = Some [1].
  Proof. vm_compute. reflexivity. Qed.

  Lemma fuel_exhaustion_is_not_an_evm_failure :
    CallRunner.run 1 (initial (call 0 0 0 50000) [0]) = None.
  Proof. vm_compute. reflexivity. Qed.

  Definition returned_bytes (result : option (InterpreterAction.t * CallFrame.state)) :=
    match result with
    | Some (_, state) => Some (List.map Integer.value
        (InstructionContext.State.interpreter _ _ _ state).(Interpreter.return_data)
          .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value))
    | None => None
    end.

  Definition memory_prefix (len : nat)
      (result : option (InterpreterAction.t * CallFrame.state)) :=
    match result with
    | Some (_, state) => Some (List.map Integer.value (List.firstn len
        (InstructionContext.State.interpreter _ _ _ state).(Interpreter.memory).(Memory.value)))
    | None => None
    end.

  Definition remaining_gas (result : option (InterpreterAction.t * CallFrame.state)) :=
    match result with
    | Some (_, state) => Some
        (InstructionContext.State.interpreter _ _ _ state)
          .(Interpreter.gas).(Gas.remaining).(Integer.value)
    | None => None
    end.

  Definition output_byte (opcode : Z) : list Z :=
    [96; 42; 96; 0; 83; 96; 1; 96; 0; opcode].

  Lemma empty_child_returns_unused_gas :
    remaining_gas (run (call 0 0 0 50000 ++ [0]) []) = Some 97379.
  Proof. vm_compute. reflexivity. Qed.

  Lemma exceptional_child_does_not_return_unused_gas :
    remaining_gas (run (call 0 0 0 50000 ++ [0]) [80]) = Some 47379.
  Proof. vm_compute. reflexivity. Qed.

  Lemma full_return_buffer_with_zero_output_range :
    returned_bytes (run (call 0 0 0 50000 ++ [0]) (output_byte 243)) = Some [42].
  Proof. vm_compute. reflexivity. Qed.

  Lemma revert_preserves_return_buffer :
    returned_bytes (run (call 0 0 1 50000 ++ [0]) (output_byte 253)) = Some [42].
  Proof. vm_compute. reflexivity. Qed.

  Lemma revert_copies_output_to_parent_memory :
    memory_prefix 1 (run (call 0 0 1 50000 ++ [0]) (output_byte 253)) = Some [42].
  Proof. vm_compute. reflexivity. Qed.

  Lemma short_return_does_not_zero_remaining_output_area :
    memory_prefix 2 (run
      ([96; 99; 96; 0; 83; 96; 88; 96; 1; 83] ++ call 0 0 2 50000 ++ [0])
      (output_byte 243)) = Some [42; 88].
  Proof. vm_compute. reflexivity. Qed.

  Lemma child_reads_caller_memory_as_calldata :
    returned_bytes (run
      ([96; 42; 96; 0; 83] ++ call 0 1 0 50000 ++ [0])
      [54; 96; 0; 96; 0; 55; 54; 96; 0; 243]) = Some [42].
  Proof. vm_compute. reflexivity. Qed.

  Lemma grandchild_write_survives_two_returns :
    storage 44 (run (call 0 0 0 50000 ++ [0])
      (call_to 44 0 0 0 30000 ++ [0])) = Some [(0, 9)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma child_revert_undoes_grandchild_write :
    storage 44 (run (call 0 0 0 50000 ++ [0])
      (call_to 44 0 0 0 30000 ++ [96; 0; 96; 0; 253])) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma unimplemented_child_opcode_is_not_call_failure :
    run (call 0 0 0 50000 ++ [0]) [250] = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma precompile_call_is_explicitly_unsupported :
    run (call_to 1 0 0 0 50000 ++ [0]) [] = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma call_gas_is_capped_from_the_actual_remaining_budget :
    let state := initial (call 0 0 0 50000 ++ [0]) [] in
    let interpreter := InstructionContext.State.interpreter _ _ _ state in
    let state : CallFrame.state :=
      {| InstructionContext.State.interpreter := interpreter
           <| @Interpreter.gas WIRE _ WIRE_types _ :=
             interpreter.(Interpreter.gas) <| Gas.limit := 10000 |> <| Gas.remaining := 10000 |> |>;
         InstructionContext.State.host := InstructionContext.State.host _ _ _ state |} in
    remaining_gas (CallRunner.run 100 state) = Some 7379.
  Proof. vm_compute. reflexivity. Qed.

  Lemma revert_returns_unspent_child_gas :
    remaining_gas (run (call 0 0 0 50000 ++ [0]) (output_byte 253)) = Some 97361.
  Proof. vm_compute. reflexivity. Qed.

  Lemma failed_transfer_returns_stipend_with_child_budget :
    remaining_gas (run (call 11 0 0 50000 ++ [0]) [0]) = Some 90679.
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_account_charge_precedes_failed_transfer :
    remaining_gas (run (call 11 0 0 50000 ++ [0]) []) = Some 65679.
  Proof. vm_compute. reflexivity. Qed.

  Definition warm_accounts (result : option (InterpreterAction.t * CallFrame.state)) :=
    match result with
    | Some (_, state) => Some
        (InstructionContext.State.host _ _ _ state).(StatefulHost.accessed_accounts)
    | None => None
    end.

  Lemma child_rollback_keeps_caller_loading_but_undoes_child_loading :
    warm_accounts (run (call 0 0 0 50000 ++ [0])
      (call_to 44 0 0 0 30000 ++ [96; 0; 96; 0; 253])) = Some [43; 42].
  Proof. vm_compute. reflexivity. Qed.

  Lemma parent_rollback_undoes_all_child_loading :
    warm_accounts (run (call 0 0 0 50000 ++ [96; 0; 96; 0; 253])
      (call_to 44 0 0 0 30000 ++ [0])) = Some [42].
  Proof. vm_compute. reflexivity. Qed.

  Definition run_without_callee (value : Z) :=
    let state := initial (call value 0 0 50000 ++ [96; 43; 63; 0]) [] in
    let host := InstructionContext.State.host _ _ _ state in
    let accounts := List.filter
      (fun account => negb (account.(StatefulHost.Account.address) =? 43))
      host.(StatefulHost.accounts) in
    let host := StatefulHost.warm_account (StatefulHost.make
      (host.(StatefulHost.input) <| StatefulHost.Input.state := accounts |>)) 42 in
    CallRunner.run 100
      {| InstructionContext.State.interpreter := InstructionContext.State.interpreter _ _ _ state;
         InstructionContext.State.host := host |}.

  Lemma newly_funded_account_has_empty_code_hash :
    stack (run_without_callee 3) = Some [StatefulHost.empty_code_hash; 1].
  Proof. vm_compute. reflexivity. Qed.

  Lemma nonexistent_account_without_transfer_still_hashes_to_zero :
    stack (run_without_callee 0) = Some [0; 1].
  Proof. vm_compute. reflexivity. Qed.
End Test.
