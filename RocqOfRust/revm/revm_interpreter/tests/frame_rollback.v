From Stdlib Require Import List ZArith.

Require Import revm.revm_interpreter.instructions.simulate.table.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.simulate.dispatch.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.frame.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.tests.stateful_dispatch.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_primitives.links.hardfork.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition before : StatefulHost.t :=
    let account := add11_account
      <| StatefulHost.Account.storage := [(0, 7)] |>
      <| StatefulHost.Account.transient_storage := [(1, 9)] |> in
    (StatefulHost.make (add11_input <| StatefulHost.Input.state := [account] |>))
      <| StatefulHost.accessed_accounts := [45] |>
      <| StatefulHost.accessed_storage := [(45, 1)] |>
      <| StatefulHost.logs := [{| StatefulHost.EvmLog.address := 45;
        StatefulHost.EvmLog.topics := [1]; StatefulHost.EvmLog.data := [2] |}] |>
      <| StatefulHost.state_changes := [StatefulHost.Change.Storage 45 1 9] |>.

  Definition should_continue (code : Bytecode.t) : bool :=
    match code.(Bytecode.action) with
    | None => bytecode_is_not_end code
    | Some _ => false
    end.

  Definition execute (fuel : nat) (gas_limit : Z) (code : list Z) :=
    let base := make_interpreter_with_bytecode
      (List.map (fun value => {| Integer.value := value |}) code)
      {| Stack.value := [] |} in
    let interpreter : Interpreter.t WIRE WIRE_types :=
      (interpreter_with_spec_id base SpecId.CANCUN)
        <| @Interpreter.gas WIRE _ WIRE_types _ :=
          base.(Interpreter.gas)
            <| Gas.limit := {| Integer.value := gas_limit |} |>
            <| Gas.remaining := {| Integer.value := gas_limit |} |> |> in
    let state : InstructionContext.State.t StatefulHost.t WIRE WIRE_types := {|
      InstructionContext.State.interpreter := interpreter;
      InstructionContext.State.host := before;
    |} in
    let table := FragmentInstructionTable.table
      (H := StatefulHost.t) (run_host := run_Host_for_StatefulHost)
      run_InterpreterTypes_for_WIRE in
    InterpreterDispatch.run_plain_stateful_fuel fuel InterpreterTypes.I
      should_continue table state.

  Definition run (gas_limit : Z) (code : list Z) :=
    StatefulFrame.finish before (execute 100 gas_limit code).

  Definition host_of (result : option (InterpreterAction.t *
      InstructionContext.State.t StatefulHost.t WIRE WIRE_types)) :=
    match result with
    | Some (_, state) => Some
        (InstructionContext.State.host StatefulHost.t WIRE WIRE_types state)
    | None => None
    end.

  Definition output_of (result : option (InterpreterAction.t *
      InstructionContext.State.t StatefulHost.t WIRE WIRE_types)) :=
    match result with
    | Some (InterpreterAction.Return output, _) =>
        Some (output.(InterpreterResult.result),
          List.map Integer.value output.(InterpreterResult.output)
            .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value))
    | _ => None
    end.

  Definition writes : list Z := [96; 8; 96; 0; 85; 96; 9; 96; 0; 85].
  Definition returning (opcode : Z) : list Z :=
    [96; 42; 96; 0; 83; 96; 1; 96; 0; opcode; 254].

  Lemma revert_restores_complete_host :
    host_of (run 100000 (writes ++ returning 253)) = Some before.
  Proof. vm_compute. reflexivity. Qed.

  Lemma revert_preserves_output :
    output_of (run 100000 (writes ++ returning 253)) =
    Some (InstructionResult.Revert, [42]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma stop_keeps_writes :
    option_map (fun host =>
      option_map StatefulHost.Account.storage
        (StatefulHost.find_account 0 host.(StatefulHost.accounts)))
      (host_of (run 100000 (writes ++ [0]))) = Some (Some [(0, 9)]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma return_keeps_writes :
    host_of (run 100000 (writes ++ returning 243)) =
    host_of (execute 100 100000 (writes ++ returning 243)).
  Proof. vm_compute. reflexivity. Qed.

  Lemma underflow_restores_host :
    host_of (run 100000 (writes ++ [80])) = Some before.
  Proof. vm_compute. reflexivity. Qed.

  Lemma underflow_reports_exact_error :
    output_of (run 100000 (writes ++ [80])) =
    Some (InstructionResult.StackUnderflow, []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_out_of_gas_restores_host :
    host_of (run 2400 writes) = Some before.
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_out_of_gas_reports_exact_error :
    output_of (run 2400 writes) = Some (InstructionResult.OutOfGas, []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma static_out_of_gas_restores_host :
    host_of (run 5007 [96; 8; 96; 0; 85; 96; 0]) = Some before.
  Proof. vm_compute. reflexivity. Qed.

  Lemma static_out_of_gas_prefix_really_writes :
    option_map (fun host =>
      option_map StatefulHost.Account.storage
        (StatefulHost.find_account 0 host.(StatefulHost.accounts)))
      (host_of (run 5007 [96; 8; 96; 0; 85; 0])) = Some (Some [(0, 8)]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma static_out_of_gas_reports_exact_error :
    output_of (run 5007 [96; 8; 96; 0; 85; 96; 0]) =
    Some (InstructionResult.OutOfGas, []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma bounds_failure_restores_host :
    host_of (run 100000 (writes ++ [96; 1; 96; 0; 96; 0; 62])) = Some before.
  Proof. vm_compute. reflexivity. Qed.

  Lemma bounds_failure_reports_exact_error :
    output_of (run 100000 (writes ++ [96; 1; 96; 0; 96; 0; 62])) =
    Some (InstructionResult.OutOfOffset, []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma exhausted_fuel_is_not_a_completed_frame :
    StatefulFrame.finish before (execute 1 100000 writes) = None.
  Proof. vm_compute. reflexivity. Qed.

  Definition outer_changes : StatefulHost.t :=
    before <| StatefulHost.accessed_accounts := [46; 45] |>
      <| StatefulHost.logs := before.(StatefulHost.logs) ++
        [{| StatefulHost.EvmLog.address := 46;
            StatefulHost.EvmLog.topics := []; StatefulHost.EvmLog.data := [3] |}] |>.

  Definition inner_changes : StatefulHost.t :=
    outer_changes
      <| StatefulHost.accounts :=
        List.map (fun account => account
          <| StatefulHost.Account.transient_storage := [(1, 10)] |>)
          outer_changes.(StatefulHost.accounts) |>
      <| StatefulHost.accessed_accounts := [47; 46; 45] |>
      <| StatefulHost.accessed_storage := [(47, 2); (45, 1)] |>
      <| StatefulHost.logs := [] |>
      <| StatefulHost.state_changes :=
        [StatefulHost.Change.TransientStorage 0 1 10] |>.

  Definition finish_host (checkpoint after : StatefulHost.t) (commit : bool) :=
    host_of (StatefulFrame.finish checkpoint
      (option_map (fun '(action, state) =>
        (action, state <| @InstructionContext.State.host
          StatefulHost.t WIRE _ _ WIRE_types _ := after |>))
        (execute 100 100000 (if commit then [0] else returning 253)))).

  Lemma inner_rollback_preserves_outer_changes :
    finish_host outer_changes inner_changes false = Some outer_changes.
  Proof. vm_compute. reflexivity. Qed.

  Lemma outer_rollback_discards_committed_inner_changes :
    match finish_host outer_changes inner_changes true with
    | Some committed => finish_host before committed false
    | None => None
    end = Some before.
  Proof. vm_compute. reflexivity. Qed.

  Lemma success_preserves_transient_storage_logs_and_warmth :
    finish_host before inner_changes true = Some inner_changes.
  Proof. vm_compute. reflexivity. Qed.

  Lemma rollback_preserves_returned_interpreter_and_gas :
    option_map (fun '(action, state) =>
      (action, InstructionContext.State.interpreter
        StatefulHost.t WIRE WIRE_types state))
      (run 100000 (writes ++ returning 253)) =
    option_map (fun '(action, state) =>
      (action, InstructionContext.State.interpreter
        StatefulHost.t WIRE WIRE_types state))
      (execute 100 100000 (writes ++ returning 253)).
  Proof. vm_compute. reflexivity. Qed.
End Test.
