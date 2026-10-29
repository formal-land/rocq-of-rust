Require Import simulate.RocqOfRust.
From Stdlib Require Import List String.
Require Import core.links.result.
Require Import revm.revm_context.simulate.context.
Require Import revm.revm_context.simulate.host.
Require Import revm.revm_context.simulate.journal.
Require Import revm.revm_context.tests.context.
Require Import revm.revm_context.tests.journal_load.
Require Import revm.revm_context_interface.simulate.context.
Require Import revm.revm_interpreter.instructions.simulate.runtime_host.
Require Import revm.revm_interpreter.interpreter.links.runtime_flags.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.

Import ListNotations.

Module DbTest := journal_load.Test.

#[local] Existing Instance DbTest.db_methods.

Module Test.
  Definition initial := context.Test.context.

  Definition interpreter : Interpreter.t WIRE WIRE_types.
  Proof.
    refine ((make_interpreter {| Stack.value := [DbTest.word 2] |})
      <| Interpreter.runtime_flag := _ |> <| Interpreter.input := _ |>).
    - exact (empty_input <| Input.target_address := DbTest.target |>).
    - exact (RuntimeFlags.non_static SpecId.OSAKA).
  Defined.

  Definition loaded :=
    snd (Impl_Host_for_Context.load_account_info_skip_cold_load initial DbTest.target false false).

  Example sload_uses_typed_journal_and_charges_cold_then_warm_cost :
    let '(first, context) := RuntimeInstructions.sload (IInterpreterTypes := InterpreterTypes.I) interpreter loaded in
    let '(second, context) := RuntimeInstructions.sload (IInterpreterTypes := InterpreterTypes.I) interpreter context in
    (first.(Interpreter.stack).(Stack.value), first.(Interpreter.gas).(Gas.remaining).(Integer.value),
      second.(Interpreter.gas).(Gas.remaining).(Integer.value), context.(Context.error),
      context.(Context.journaled_state).(Journal.database).(DbTest.reads)) =
      ([DbTest.word 7], 997900, 999900, Result.Ok tt, [DbTest.Basic; DbTest.Storage]).
  Proof. vm_compute. reflexivity. Qed.

  Example cold_sload_without_enough_gas_does_not_read_database :
    let interpreter := interpreter <| Interpreter.gas := interpreter.(Interpreter.gas)
      <| Gas.remaining := 1999 |> |> in
    let '(_, context) := RuntimeInstructions.sload (IInterpreterTypes := InterpreterTypes.I) interpreter loaded in
    (context.(Context.error), context.(Context.journaled_state).(Journal.database).(DbTest.reads)) =
      (Result.Ok tt, [DbTest.Basic]).
  Proof. vm_compute. reflexivity. Qed.

  Example unloaded_storage_account_is_an_internal_failure :
    let '(_, context) := RuntimeInstructions.sload (IInterpreterTypes := InterpreterTypes.I) interpreter initial in
    context.(Context.error) = Result.Err (ContextError.Custom "journal invariant failure").
  Proof. vm_compute. reflexivity. Qed.
End Test.
