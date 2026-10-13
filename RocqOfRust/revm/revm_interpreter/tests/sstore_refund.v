From Stdlib Require Import List ZArith.

Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.instructions.simulate.host.sstore.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
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
  Definition values (original present new : Z) : SStoreResult.t := {|
    SStoreResult.original_value := StatefulHost.rust_word original;
    SStoreResult.present_value := StatefulHost.rust_word present;
    SStoreResult.new_value := StatefulHost.rust_word new;
  |}.

  (** Independent native branch vectors: unchanged, clean clearing, dirty
      clearing, clearing cancellation and restoration of the original value. *)
  Lemma frontier_refund_vectors :
    List.map (fun vals => (sstore_refund SpecId.FRONTIER vals).(Integer.value))
      [values 1 1 0; values 0 1 0; values 1 0 1; values 1 1 1] =
      [15000; 15000; 0; 0].
  Proof. vm_compute. reflexivity. Qed.

  Lemma istanbul_refund_vectors :
    List.map (fun vals => (sstore_refund SpecId.ISTANBUL vals).(Integer.value))
      [values 1 1 1; values 1 1 0; values 1 2 0; values 1 0 2;
       values 1 0 1; values 1 2 1; values 0 1 0; values 0 1 2] =
      [0; 15000; 15000; -15000; -10800; 4200; 19200; 0].
  Proof. vm_compute. reflexivity. Qed.

  Lemma berlin_refund_vectors :
    List.map (fun vals => (sstore_refund SpecId.BERLIN vals).(Integer.value))
      [values 1 1 1; values 1 1 0; values 1 2 0; values 1 0 2;
       values 1 0 1; values 1 2 1; values 0 1 0; values 0 1 2] =
      [0; 15000; 15000; -15000; -12200; 2800; 19900; 0].
  Proof. vm_compute. reflexivity. Qed.

  Lemma london_through_osaka_refund_vectors :
    List.map (fun spec =>
      List.map (fun vals => (sstore_refund spec vals).(Integer.value))
        [values 1 1 1; values 1 1 0; values 1 2 0; values 1 0 2;
         values 1 0 1; values 1 2 1; values 0 1 0; values 0 1 2])
      [SpecId.LONDON; SpecId.CANCUN; SpecId.PRAGUE; SpecId.OSAKA] =
      List.repeat [0; 4800; 4800; -4800; -2000; 2800; 19900; 0] 4.
  Proof. vm_compute. reflexivity. Qed.

  Definition execute_write
      (spec : SpecId.t) (original present new previous_refund : Z) :=
    let original_account := add11_account
      <| StatefulHost.Account.storage := [(0, original)] |> in
    let present_account := add11_account
      <| StatefulHost.Account.storage := [(0, present)] |> in
    let host := StatefulHost.with_accounts
      (StatefulHost.make
        (add11_input <| StatefulHost.Input.state := [original_account] |>))
      [present_account] in
    let interpreter := interpreter_with_spec_id
      (make_interpreter
        {| Stack.value := [StatefulHost.rust_word 0; StatefulHost.rust_word new] |})
      spec in
    let interpreter := interpreter
      <| @Interpreter.gas WIRE _ WIRE_types _ :=
        interpreter.(Interpreter.gas)
          <| Gas.refunded := {| Integer.value := previous_refund |} |> |> in
    let '(interpreter, host) :=
      sstore (IInterpreterTypes := InterpreterTypes.I)
        (IHost := StatefulHost.HostForRevmHost) interpreter host in
    (interpreter.(Interpreter.gas).(Gas.refunded).(Integer.value),
     option_map (fun account =>
       StatefulHost.lookup_word 0 account.(StatefulHost.Account.storage))
       (StatefulHost.find_account 0 host.(StatefulHost.accounts))).

  Lemma clearing_records_refund_and_storage :
    execute_write SpecId.CANCUN 1 1 0 0 = (4800, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma restoring_subtracts_previous_clear_and_adds_reset_refund :
    execute_write SpecId.PRAGUE 1 0 1 4800 = (2800, Some 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma dirty_clear_cancellation_is_signed :
    execute_write SpecId.OSAKA 1 0 2 0 = (-4800, Some 2).
  Proof. vm_compute. reflexivity. Qed.

  Lemma resetting_original_zero_records_uncapped_refund :
    execute_write SpecId.CANCUN 0 1 0 0 = (19900, Some 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma unchanged_write_keeps_existing_refund :
    execute_write SpecId.PRAGUE 1 1 1 4800 = (4800, Some 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma pre_berlin_branch_records_refund :
    execute_write SpecId.ISTANBUL 1 1 0 0 = (15000, Some 0).
  Proof. vm_compute. reflexivity. Qed.
End Test.
