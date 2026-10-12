From Stdlib Require Import List ZArith.

Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import bytes.links.bytes.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.call_frame.
Require Import revm.revm_interpreter.tests.call_runner.
Require Import revm.revm_interpreter.tests.calls.
Require Import revm.revm_interpreter.tests.identity_precompile.
Require Import revm.revm_interpreter.tests.precompile_frame.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_precompile.tests.blake2.
Require Import revm.revm_primitives.links.hardfork.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition call (opcode value input_size output_offset output_size gas : Z) :=
    identity_precompile.Test.call opcode 9 value input_size output_offset output_size gas.

  Definition initial (program : list Z) : CallFrame.state :=
    let state := calls.Test.initial program [] in
    {| InstructionContext.State.interpreter := InstructionContext.State.interpreter _ _ _ state;
       InstructionContext.State.host := StatefulHost.warm_account
         (InstructionContext.State.host _ _ _ state) 9 |}.

  Definition run (program : list Z) := CallRunner.run 300 (initial program).

  Definition owned_inputs (data : list Z) (gas : Z) : CallInputs.t :=
    identity_precompile.Test.owned_inputs
      <| CallInputs.input := CallInput.Bytes
        (Impl_Bytes.copy_from_slice (List.map StatefulHost.rust_byte data)) |>
      <| CallInputs.gas_limit := {| Integer.value := gas |} |>
      <| CallInputs.bytecode_address := StatefulHost.rust_address 9 |>
      <| CallInputs.target_address := StatefulHost.rust_address 9 |>.

  Definition direct (data : list Z) (gas : Z) : InterpreterResult.t :=
    let parent := InstructionContext.State.interpreter _ _ _ (initial [0]) in
    PrecompileFrame.blake2 (CallFrame.child parent (owned_inputs data gas) []).

  Definition direct_observation (result : InterpreterResult.t) :=
    (result.(InterpreterResult.result),
     result.(InterpreterResult.gas).(Gas.remaining).(Integer.value),
     List.map Integer.value result.(InterpreterResult.output)
       .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value)).

  Lemma exact_gas_consumed :
    let result := direct revm.revm_precompile.tests.blake2.Test.input_1 12 in
    (result.(InterpreterResult.result), result.(InterpreterResult.gas).(Gas.remaining).(Integer.value),
      List.length result.(InterpreterResult.output).(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value)) =
      (InstructionResult.Return, 0, 64%nat).
  Proof. vm_compute. reflexivity. Qed.
  Lemma insufficient_gas :
    direct_observation (direct revm.revm_precompile.tests.blake2.Test.input_1 11) =
      (InstructionResult.PrecompileOOG, 11, []).
  Proof. vm_compute. reflexivity. Qed.
  Lemma malformed_input : direct_observation (direct [] 100) =
      (InstructionResult.PrecompileError, 100, []).
  Proof. vm_compute. reflexivity. Qed.
  Lemma istanbul_activation :
    (PrecompileFrame.is_precompile SpecId.PETERSBURG 9,
     PrecompileFrame.is_precompile SpecId.ISTANBUL 9,
     PrecompileFrame.supported 9) = (false, true, true).
  Proof. vm_compute. reflexivity. Qed.
End Test.
