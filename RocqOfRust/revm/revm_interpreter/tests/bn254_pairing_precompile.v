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
Require Import revm.revm_interpreter.tests.stateful_dispatch.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_primitives.links.hardfork.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition initial (program : list Z) : CallFrame.state :=
    let state := calls.Test.initial program [] in
    {| InstructionContext.State.interpreter := InstructionContext.State.interpreter _ _ _ state;
       InstructionContext.State.host := StatefulHost.warm_account
         (InstructionContext.State.host _ _ _ state) 8 |}.

  Definition owned_inputs (data : list Z) (gas : Z) : CallInputs.t :=
    identity_precompile.Test.owned_inputs
      <| CallInputs.input := CallInput.Bytes
        (Impl_Bytes.copy_from_slice (List.map StatefulHost.rust_byte data)) |>
      <| CallInputs.gas_limit := {| Integer.value := gas |} |>
      <| CallInputs.bytecode_address := StatefulHost.rust_address 8 |>
      <| CallInputs.target_address := StatefulHost.rust_address 8 |>.

  Definition direct (spec : SpecId.t) (data : list Z) (gas : Z) : InterpreterResult.t :=
    let parent := InstructionContext.State.interpreter _ _ _ (initial [0]) in
    let child := CallFrame.child parent (owned_inputs data gas) [] in
    PrecompileFrame.bn254_pairing
      (stateful_dispatch.interpreter_with_spec_id child spec).

  Definition observe (result : InterpreterResult.t) :=
    (result.(InterpreterResult.result),
     result.(InterpreterResult.gas).(Gas.remaining).(Integer.value),
     List.map Integer.value result.(InterpreterResult.output)
       .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value)).

  Lemma activation :
    (PrecompileFrame.is_precompile SpecId.SPURIOUS_DRAGON 8,
     PrecompileFrame.is_precompile SpecId.BYZANTIUM 8,
     PrecompileFrame.supported 8) = (false, true, true).
  Proof. vm_compute. reflexivity. Qed.

  Lemma byzantium_empty_cost :
    observe (direct SpecId.BYZANTIUM [] 100000) =
      (InstructionResult.Return, 0, List.repeat 0 31 ++ [1]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma istanbul_empty_cost :
    observe (direct SpecId.ISTANBUL [] 45000) =
      (InstructionResult.Return, 0, List.repeat 0 31 ++ [1]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_out_of_gas :
    observe (direct SpecId.ISTANBUL [] 44999) =
      (InstructionResult.PrecompileOOG, 44999, []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma malformed_length :
    observe (direct SpecId.ISTANBUL (List.repeat 0 191) 45000) =
      (InstructionResult.PrecompileError, 45000, []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma malformed_length_out_of_gas_first :
    observe (direct SpecId.ISTANBUL (List.repeat 0 193) 78999) =
      (InstructionResult.PrecompileOOG, 78999, []).
  Proof. vm_compute. reflexivity. Qed.

  Definition run (program : list Z) := CallRunner.run 300 (initial program).

  Lemma all_call_schemes_dispatch :
    List.map (fun opcode =>
      let result := run
        (identity_precompile.Test.call opcode 8 0 0 128 32 45000 ++ [0]) in
      (calls.Test.stack result, calls.Test.returned_bytes result))
      [241; 242; 244; 250] =
    List.repeat (Some [1], Some (List.repeat 0 31 ++ [1])) 4.
  Proof. vm_compute. reflexivity. Qed.
End Test.
