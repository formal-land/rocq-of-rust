From Stdlib Require Import List ZArith.
Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.bits.links.address.
Require Import core.links.result.
Require Import core.ops.links.range.
Require Import revm.revm_context.simulate.context.
Require Import revm.revm_context.simulate.cfg.
Require Import revm.revm_handler.simulate.precompile_provider.
Require Import revm.revm_handler.tests.typed_frames.
Require Import revm.revm_interpreter.simulate.eth_types.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter_InterpreterResult.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_primitives.links.hardfork.
Import ListNotations.

Module Test.
  Definition run_input (spec : SpecId.t) (address : u64) (memory : Memory.t)
      (input : CallInput.t) (gas : u64) : option InterpreterResult.t :=
    let ctx := typed_frames.Test.initial in
    let ctx := ctx <| Context.cfg := ctx.(Context.cfg) <| CfgEnv.spec := spec |> |> in
    let inputs := (typed_frames.Test.inputs [])
      <| CallInputs.bytecode_address := {| Address.value := address.(Integer.value) |} |>
      <| CallInputs.input := input |> <| CallInputs.gas_limit := gas |> in
    match EthPrecompiles.run ctx memory inputs with
    | Some (Result.Ok result, _) => result
    | _ => None
    end.

  Definition direct (spec : SpecId.t) (address : u64) (input : list u8) (gas : u64)
      : option InterpreterResult.t :=
    run_input spec address typed_frames.Test.empty_memory
      (CallInput.Bytes (Impl_Bytes.copy_from_slice input)) gas.

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

  Lemma p256_invalid_signature_returns_empty_success :
    observe (direct SpecId.OSAKA 256 (List.repeat (0 : u8) 160) 6900) =
      Some (InstructionResult.Return, {| Integer.value := 0 |}, 0%nat).
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

  Lemma bls_g1_infinity_addition_returns_output :
    observe (direct SpecId.OSAKA 11 (List.repeat (0 : u8) 256) 375) =
      Some (InstructionResult.Return, {| Integer.value := 0 |}, 128%nat).
  Proof. vm_compute. reflexivity. Qed.

  Lemma available_shared_input_is_consumed :
    observe (run_input SpecId.OSAKA 256
      {| Memory.value := []; Memory.shared_buffer := List.repeat (0 : u8) 160 |}
      (CallInput.SharedBuffer {| Range.start := (0 : usize); Range.end_ := (160 : usize) |})
      100000) = Some (InstructionResult.Return, {| Integer.value := 93100 |}, 0%nat).
  Proof. vm_compute. reflexivity. Qed.

  (** Rust's unavailable shared slice supplies empty input to the provider. *)
  Lemma unavailable_shared_input_is_empty :
    observe (run_input SpecId.OSAKA 256 typed_frames.Test.empty_memory
      (CallInput.SharedBuffer {| Range.start := (0 : usize); Range.end_ := (160 : usize) |})
      100000) = Some (InstructionResult.Return, {| Integer.value := 93100 |}, 0%nat).
  Proof. vm_compute. reflexivity. Qed.
End Test.
