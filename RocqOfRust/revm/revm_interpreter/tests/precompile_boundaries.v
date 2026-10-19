From Stdlib Require Import List ZArith.

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
Require Import revm.revm_interpreter.tests.calls.
Require Import revm.revm_interpreter.tests.identity_precompile.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.tests.precompile_frame.
Require Import revm.revm_primitives.links.hardfork.
Require Import simulate.RocqOfRust.

Import ListNotations.

Module Test.
  Definition direct (spec : SpecId.t) (address : u64) (input : list u8) (gas : u64)
      : option InterpreterResult.t :=
    let parent := InstructionContext.State.interpreter _ _ _ (calls.Test.initial [0%Z] []) in
    let inputs := identity_precompile.Test.owned_inputs
      <| CallInputs.input := CallInput.Bytes (Impl_Bytes.copy_from_slice input) |>
      <| CallInputs.gas_limit := gas |> in
    let child := CallFrame.child parent inputs [] in
    let child := child <| @Interpreter.runtime_flag WIRE _ WIRE_types _ :=
      child.(Interpreter.runtime_flag) <| RuntimeFlags.spec_id := spec |> |> in
    PrecompileFrame.run address.(Integer.value) child.

  Definition observe (result : option InterpreterResult.t) :=
    option_map (fun result =>
      (result.(InterpreterResult.result), result.(InterpreterResult.gas).(Gas.remaining),
       List.length result.(InterpreterResult.output)
         .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value))) result.

  Lemma p256_exact_gas_returns_empty_success :
    observe (direct SpecId.OSAKA 256 [] 6900) =
      Some (InstructionResult.Return, {| Integer.value := 0 |}, 0%nat).
  Proof. vm_compute. reflexivity. Qed.

  Lemma p256_preserves_unspent_gas :
    observe (direct SpecId.OSAKA 256 (List.repeat (17 : u8) 256) 100000) =
      Some (InstructionResult.Return, {| Integer.value := 93100 |}, 0%nat).
  Proof. vm_compute. reflexivity. Qed.

  Lemma p256_short_gas_is_failure :
    observe (direct SpecId.OSAKA 256 [] 6899) =
      Some (InstructionResult.PrecompileOOG, {| Integer.value := 6899 |}, 0%nat).
  Proof. vm_compute. reflexivity. Qed.

  Lemma p256_crypto_stays_incomplete :
    direct SpecId.OSAKA 256 (List.repeat (0 : u8) 160) 6900 = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma p256_is_not_enabled_before_osaka :
    direct SpecId.PRAGUE 256 [] 6900 = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma bls_is_not_enabled_before_prague :
    direct SpecId.CANCUN 11 [] 0 = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma all_bls_fixture_inputs_reject :
    List.map (fun address => observe
      (direct SpecId.OSAKA address (List.repeat (17 : u8) 256) 100000))
      (List.map (fun value => ({| Integer.value := value |} : u64)) [11; 12; 13; 14; 15; 16; 17]) =
    List.repeat (Some (InstructionResult.PrecompileError,
      {| Integer.value := 100000 |}, 0%nat)) 7.
  Proof. vm_compute. reflexivity. Qed.

  Lemma bls_valid_encoding_stays_incomplete :
    direct SpecId.OSAKA 11 (List.repeat (0 : u8) 256) 375 = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma unresolved_shared_input_stays_incomplete :
    let child := InstructionContext.State.interpreter _ _ _ (calls.Test.initial [0%Z] []) in
    let child := child <| @Interpreter.input WIRE _ WIRE_types _ :=
      child.(Interpreter.input) <| Input.input := CallInput.SharedBuffer
        {| Range.start := {| Integer.value := 0 |};
           Range.end_ := {| Integer.value := 160 |} |} |> |> in
    PrecompileFrame.partial_precompile 256 child = None.
  Proof. reflexivity. Qed.
End Test.
