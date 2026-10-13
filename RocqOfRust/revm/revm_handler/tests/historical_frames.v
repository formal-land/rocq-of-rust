From Stdlib Require Import List ZArith.

Require Import alloy_primitives.bytes.simulate.mod.
Require Import revm.revm_context_interface.links.cfg.
Require Import revm.revm_handler.simulate.legacy_call.
Require Import revm.revm_interpreter.interpreter_action.links.create_inputs.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_InterpreterResult.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.call_frame.
Require Import revm.revm_interpreter.tests.create_frame.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.tests.precompile_frame.
Require Import revm.revm_interpreter.tests.stateful_dispatch.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module HistoricalFramesTest.
  Definition host (spec : SpecId.t) :=
    (StatefulHost.make (add11_input <| StatefulHost.Input.state :=
      [StatefulHost.empty_account 42; StatefulHost.empty_account 43] |>))
      <| StatefulHost.spec_id := spec |>.

  Definition creation_inputs : CreateInputs.t := {|
    CreateInputs.caller := StatefulHost.rust_address 42;
    CreateInputs.scheme := CreateScheme.Create;
    CreateInputs.value := {| Uint.value := 0 |};
    CreateInputs.init_code := Impl_Bytes.new;
    CreateInputs.gas_limit := 1000;
  |}.

  Definition created_nonce (spec : SpecId.t) :=
    match CreateFrame.prepare (make_interpreter_with_bytecode [] {| Stack.value := [] |})
      (host spec) 0 creation_inputs with
    | Some (CreateFrame.Child address _ state) =>
      option_map StatefulHost.Account.nonce (StatefulHost.find_account address
        (InstructionContext.State.host _ _ _ state).(StatefulHost.accounts))
    | _ => None
    end.

  Lemma created_nonce_starts_with_eip161 :
    List.map created_nonce [SpecId.FRONTIER; SpecId.HOMESTEAD; SpecId.TANGERINE;
      SpecId.SPURIOUS_DRAGON; SpecId.CANCUN] = [Some 0; Some 0; Some 0; Some 1; Some 1].
  Proof. vm_compute. reflexivity. Qed.

  Definition finish (spec : SpecId.t) (code : list Z) (gas : Z) :=
    CreateFrame.finish 43 (host spec) (host spec) {|
      InterpreterResult.result := InstructionResult.Return;
      InterpreterResult.output := Impl_Bytes.copy_from_slice (List.map StatefulHost.rust_byte code);
      InterpreterResult.gas := Impl_Gas.new {| Integer.value := gas |};
    |}.

  Definition finish_status spec code gas :=
    (fst (finish spec code gas)).(InterpreterResult.result).

  Lemma ef_prefix_activates_in_london :
    finish_status SpecId.BERLIN [239] 200 = InstructionResult.Return /\
    finish_status SpecId.LONDON [239] 200 = InstructionResult.CreateContractStartingWithEF.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma size_limit_activates_in_spurious_dragon :
    finish_status SpecId.HOMESTEAD (List.repeat 0 24577) 0 = InstructionResult.OutOfGas /\
    finish_status SpecId.TANGERINE (List.repeat 0 24577) 0 = InstructionResult.OutOfGas /\
    finish_status SpecId.SPURIOUS_DRAGON (List.repeat 0 24577) 0 =
      InstructionResult.CreateContractSizeLimit.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Lemma frontier_unfunded_code_deposit_keeps_empty_contract :
    let '(output, result_host) := finish SpecId.FRONTIER [0] 199 in
    output.(InterpreterResult.result) = InstructionResult.Return /\
    output.(InterpreterResult.output) = Impl_Bytes.new /\
    output.(InterpreterResult.gas).(Gas.remaining) = 199 /\
    option_map StatefulHost.Account.code
      (StatefulHost.find_account 43 result_host.(StatefulHost.accounts)) = Some [].
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Lemma homestead_unfunded_code_deposit_fails :
    finish_status SpecId.HOMESTEAD [0] 199 = InstructionResult.OutOfGas.
  Proof. vm_compute. reflexivity. Qed.

  Lemma frontier_funded_code_deposit_keeps_code :
    let '(output, result_host) := finish SpecId.FRONTIER [0] 200 in
    output.(InterpreterResult.result) = InstructionResult.Return /\
    output.(InterpreterResult.gas).(Gas.remaining) = 0 /\
    option_map StatefulHost.Account.code
      (StatefulHost.find_account 43 result_host.(StatefulHost.accounts)) = Some [0].
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Lemma touched_empty_accounts_cleared_from_spurious_dragon :
    List.map StatefulHost.Account.address
      (LegacyCall.finish_accounts [43] (host SpecId.TANGERINE)) = [42; 43] /\
    List.map StatefulHost.Account.address
      (LegacyCall.finish_accounts [43] (host SpecId.SPURIOUS_DRAGON)) = [42].
  Proof. vm_compute. split; reflexivity. Qed.

  Definition zero_transfer_target spec :=
    let '(_, result_host) := CallFrame.transfer (host spec) 42 44 0 in
    StatefulHost.find_account 44 (LegacyCall.finish_accounts result_host.(StatefulHost.touched_accounts)
      result_host).

  Lemma zero_transfer_creates_missing_account_before_spurious_dragon :
    option_map StatefulHost.Account.address (zero_transfer_target SpecId.TANGERINE) = Some 44 /\
    zero_transfer_target SpecId.SPURIOUS_DRAGON = None.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma existing_empty_account_is_not_new_before_spurious_dragon :
    StatefulHost.state_clear_aware_is_empty (host SpecId.TANGERINE) 43 = false /\
    StatefulHost.state_clear_aware_is_empty (host SpecId.SPURIOUS_DRAGON) 43 = true.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma missing_account_is_new_before_and_after_spurious_dragon :
    StatefulHost.state_clear_aware_is_empty (host SpecId.TANGERINE) 44 = true /\
    StatefulHost.state_clear_aware_is_empty (host SpecId.SPURIOUS_DRAGON) 44 = true.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma touched_missing_account_is_not_new_before_spurious_dragon :
    StatefulHost.state_clear_aware_is_empty
      (StatefulHost.touch_account (host SpecId.TANGERINE) 44) 44 = false /\
    StatefulHost.state_clear_aware_is_empty
      (StatefulHost.touch_account (host SpecId.SPURIOUS_DRAGON) 44) 44 = true.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma historical_header_fields_have_activation_boundaries :
    LegacyCall.validate_header SpecId.LONDON None None = None /\
    LegacyCall.validate_header SpecId.MERGE None None = Some LegacyCall.Rejection.PrevrandaoNotSet /\
    LegacyCall.validate_header SpecId.MERGE (Some 0) None = None /\
    LegacyCall.validate_header SpecId.SHANGHAI (Some 0) None = None /\
    LegacyCall.validate_header SpecId.CANCUN (Some 0) None = Some LegacyCall.Rejection.ExcessBlobGasNotSet /\
    LegacyCall.validate_header SpecId.CANCUN (Some 0) (Some 0) = None.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Lemma historical_precompile_sets :
    List.map (fun spec => Z.of_nat (List.length (PrecompileFrame.addresses spec)))
      [SpecId.FRONTIER; SpecId.HOMESTEAD; SpecId.SPURIOUS_DRAGON;
       SpecId.BYZANTIUM; SpecId.PETERSBURG; SpecId.ISTANBUL;
       SpecId.BERLIN; SpecId.SHANGHAI; SpecId.CANCUN; SpecId.PRAGUE; SpecId.OSAKA] =
      [4; 4; 4; 8; 8; 9; 9; 9; 10; 17; 18].
  Proof. vm_compute. reflexivity. Qed.
End HistoricalFramesTest.
