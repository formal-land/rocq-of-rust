From Stdlib Require Import List ZArith.

Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import bytes.links.bytes.
Require Import revm.revm_context_interface.links.cfg.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.interpreter_action.links.create_inputs.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.call_frame.
Require Import revm.revm_interpreter.tests.call_runner.
Require Import revm.revm_interpreter.tests.calls.
Require Import revm.revm_interpreter.tests.create_address.
Require Import revm.revm_interpreter.tests.create_frame.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition memory_code (code : list Z) : list Z :=
    List.flat_map (fun pair => [96; snd pair; 96; fst pair; 83])
      (List.combine (List.map Z.of_nat (List.seq 0 (List.length code))) code).

  Definition program (create2 : bool) (code : list Z) (value : Z) (tail : list Z) :=
    memory_code code ++ (if create2 then [96; 0] else []) ++
    [96; Z.of_nat (List.length code); 96; 0; 96; value;
     if create2 then 245 else 240] ++ tail.

  Definition initial (code : list Z) : CallFrame.state :=
    let state := calls.Test.initial code [] in
    let host := InstructionContext.State.host _ _ _ state in
    let host := StatefulHost.with_accounts host
      (StatefulHost.update_account 42 (fun account =>
        CreateFrame.with_nonce (StatefulHost.account_with_balance account 100) 7)
        host.(StatefulHost.accounts)) in
    {| InstructionContext.State.interpreter :=
         (InstructionContext.State.interpreter _ _ _ state)
           <| @Interpreter.return_data WIRE _ WIRE_types _ :=
             Impl_Bytes.copy_from_slice [StatefulHost.rust_byte 99] |>;
       InstructionContext.State.host := host |}.

  Definition run (create2 : bool) (code : list Z) (value : Z) (tail : list Z) :=
    CallRunner.run 2000 (initial (program create2 code value tail)).

  Definition address (create2 : bool) (code : list Z) : Z :=
    match (if create2 then CreateAddress.create2 42 0 code else CreateAddress.create 42 7) with
    | Some address => address | None => 0 end.

  Definition account (address : Z) (result : option (InterpreterAction.t * CallFrame.state)) :=
    match result with
    | Some (_, state) => StatefulHost.find_account address
        (InstructionContext.State.host _ _ _ state).(StatefulHost.accounts)
    | None => None end.

  Definition nonce (address : Z) result := option_map StatefulHost.Account.nonce (account address result).
  Definition code (address : Z) result := option_map StatefulHost.Account.code (account address result).
  Definition return_data (result : option (InterpreterAction.t * CallFrame.state)) := match result with
    | Some (_, state) => Some (List.map Integer.value
        (InstructionContext.State.interpreter _ _ _ state).(Interpreter.return_data)
          .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.links.bytes.Bytes.value))
    | None => None end.

  Definition deploy_stop := [96; 1; 96; 0; 243].
  Definition revert_two := [96; 2; 96; 0; 83; 96; 1; 96; 0; 253].

  Lemma create_deploys_code_and_returns_address :
    calls.Test.stack (run false deploy_stop 3 [0]) = Some [address false deploy_stop] /\
    code (address false deploy_stop) (run false deploy_stop 3 [0]) = Some [0].
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma create_updates_nonces_and_balances :
    nonce 42 (run false deploy_stop 3 [0]) = Some 8 /\
    nonce (address false deploy_stop) (run false deploy_stop 3 [0]) = Some 1 /\
    calls.Test.balance 42 (run false deploy_stop 3 [0]) = Some 97 /\
    calls.Test.balance (address false deploy_stop) (run false deploy_stop 3 [0]) = Some 3.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Lemma successful_create_clears_return_data :
    return_data (run false deploy_stop 0 [0]) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma create2_deploys_to_salted_address :
    calls.Test.stack (run true deploy_stop 0 [0]) = Some [address true deploy_stop] /\
    code (address true deploy_stop) (run true deploy_stop 0 [0]) = Some [0].
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma successful_creation_charges_initcode_and_deposit_gas :
    calls.Test.remaining_gas (run false deploy_stop 0 [0]) = Some 67732 /\
    calls.Test.remaining_gas (run true deploy_stop 0 [0]) = Some 67723.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma revert_keeps_nonce_but_restores_value :
    calls.Test.stack (run false revert_two 3 [0]) = Some [0] /\
    nonce 42 (run false revert_two 3 [0]) = Some 8 /\
    calls.Test.balance 42 (run false revert_two 3 [0]) = Some 100 /\
    account (address false revert_two) (run false revert_two 3 [0]) = None /\
    return_data (run false revert_two 3 [0]) = Some [2].
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Lemma parent_revert_restores_nonce_and_created_account :
    nonce 42 (run false deploy_stop 3 [96; 0; 96; 0; 253]) = Some 7 /\
    calls.Test.balance 42 (run false deploy_stop 3 [96; 0; 96; 0; 253]) = Some 100 /\
    account (address false deploy_stop) (run false deploy_stop 3 [96; 0; 96; 0; 253]) = None.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Lemma insufficient_funds_does_not_increment_nonce :
    calls.Test.stack (run false [] 101 [0]) = Some [0] /\
    nonce 42 (run false [] 101 [0]) = Some 7.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma constructor_storage_survives_success :
    calls.Test.storage (address false [])
      (run false [96; 9; 96; 0; 85; 0] 0 [0]) = Some [(0, 9)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma creation_gas_word_boundaries :
    List.map (fun len => option_map Integer.value (create2_cost {| Integer.value := len |})) [0; 32; 33] =
      [Some 32000; Some 32006; Some 32012] /\
    List.map (fun len => Integer.value (initcode_cost {| Integer.value := len |})) [0; 32; 33] = [0; 2; 4].
  Proof. vm_compute. split; reflexivity. Qed.

  Definition host := InstructionContext.State.host _ _ _ (initial []).
  Definition parent :=
    let interpreter := InstructionContext.State.interpreter _ _ _ (initial []) in
    interpreter <| @Interpreter.gas WIRE _ WIRE_types _ :=
      interpreter.(Interpreter.gas) <| Gas.remaining := 50000 |> |>.
  Definition inputs :=
    {| CreateInputs.caller := StatefulHost.rust_address 42;
       CreateInputs.scheme := CreateScheme.Create;
       CreateInputs.value := StatefulHost.rust_word 3;
       CreateInputs.init_code := Impl_Bytes.new;
       CreateInputs.gas_limit := 50000 |}.
  Definition immediate_observation (host : StatefulHost.t) :=
    match CreateFrame.prepare parent host 1 inputs with
    | Some (CreateFrame.Immediate output host) =>
        Some (output.(InterpreterResult.result),
          option_map StatefulHost.Account.nonce (StatefulHost.find_account 42 host.(StatefulHost.accounts)),
          CallFrame.balance host 42,
          List.existsb (Z.eqb (address false [])) host.(StatefulHost.accessed_accounts),
          List.map Uint.value (CreateFrame.resume parent None output).(Interpreter.stack).(Stack.value),
          (CreateFrame.resume parent None output).(Interpreter.gas).(Gas.remaining).(Integer.value))
    | _ => None end.

  Lemma depth_limit_rejects_before_state_changes :
    CreateFrame.prepare parent host 1025 inputs =
      Some (CreateFrame.Immediate (CreateFrame.result inputs InstructionResult.CallTooDeep) host).
  Proof. vm_compute. reflexivity. Qed.

  Definition collision_host := StatefulHost.with_accounts host
    (StatefulHost.update_account (address false []) (fun account => CreateFrame.with_nonce account 1)
      host.(StatefulHost.accounts)).
  Lemma collision_keeps_nonce_and_warmth_consumes_forwarded_gas :
    immediate_observation collision_host =
      Some (InstructionResult.CreateCollision, Some 8, 100, true, [0], 50000).
  Proof. vm_compute. reflexivity. Qed.

  Definition overflow_host := StatefulHost.with_accounts host
    (StatefulHost.update_account 42 (fun account => CreateFrame.with_nonce account (2 ^ 64 - 1))
      host.(StatefulHost.accounts)).
  Lemma nonce_overflow_returns_zero_and_unused_gas :
    immediate_observation overflow_host =
      Some (InstructionResult.Return, Some (2 ^ 64 - 1), 100, false, [0], 100000).
  Proof. vm_compute. reflexivity. Qed.

  Definition deployed_output (code : list Z) (gas : Z) :=
    {| InterpreterResult.result := InstructionResult.Return;
       InterpreterResult.output := Impl_Bytes.copy_from_slice (List.map StatefulHost.rust_byte code);
       InterpreterResult.gas := Impl_Gas.new {| Integer.value := gas |} |}.
  Definition finish_result code gas :=
    let '(output, final_host) := CreateFrame.finish 999 host
      (StatefulHost.with_accounts host (StatefulHost.empty_account 999 :: host.(StatefulHost.accounts)))
      (deployed_output code gas) in
    (output.(InterpreterResult.result), StatefulHost.find_account 999 final_host.(StatefulHost.accounts)).

  Lemma forbidden_code_rolls_back_deployment :
    finish_result [239] 1000 = (InstructionResult.CreateContractStartingWithEF, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma deposit_out_of_gas_rolls_back_deployment :
    finish_result [0] 199 = (InstructionResult.OutOfGas, None).
  Proof. vm_compute. reflexivity. Qed.

  Lemma oversized_code_rolls_back_deployment :
    finish_result (List.repeat 0 24577) 10000000 = (InstructionResult.CreateContractSizeLimit, None).
  Proof. vm_compute. reflexivity. Qed.

  Definition static_attempt (create2 : bool) :=
    calls.Test.run [96; 0; 96; 0; 96; 0; 96; 0; 96; 43; 97; 195; 80; 250; 0]
      (program create2 [] 0 [0]).

  Lemma staticcall_rejects_both_creation_schemes :
    calls.Test.stack (static_attempt false) = Some [0] /\
    calls.Test.stack (static_attempt true) = Some [0] /\
    nonce 43 (static_attempt false) = Some 0 /\
    nonce 43 (static_attempt true) = Some 0 /\
    calls.Test.balance 43 (static_attempt false) = Some 0 /\
    calls.Test.balance 43 (static_attempt true) = Some 0.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Lemma pc_and_codesize_observe_original_code :
    calls.Test.stack (calls.Test.run [88; 56; 0] []) = Some [3; 0] /\
    calls.Test.remaining_gas (calls.Test.run [88; 56; 0] []) = Some 99996.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma pc_after_jump_is_instruction_position :
    calls.Test.stack (calls.Test.run [96; 4; 86; 0; 91; 88; 0] []) = Some [5].
  Proof. vm_compute. reflexivity. Qed.

  Lemma context_instructions_each_cost_two_gas :
    calls.Test.remaining_gas (calls.Test.run [88; 0] []) = Some 99998 /\
    calls.Test.remaining_gas (calls.Test.run [56; 0] []) = Some 99998.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma codesize_does_not_count_push_padding :
    calls.Test.stack (calls.Test.run [56; 96] []) = Some [0; 2].
  Proof. vm_compute. reflexivity. Qed.

  Definition context_constructor :=
    [88; 96; 0; 85; 56; 96; 1; 85; 96; 1; 96; 0; 243].

  Lemma constructor_context_is_not_parent_or_deployed_code :
    calls.Test.storage (address false context_constructor)
      (run false context_constructor 0 [0]) = Some [(0, 0); (1, 13)] /\
    code (address false context_constructor)
      (run false context_constructor 0 [0]) = Some [0].
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma create2_constructor_uses_same_code_context :
    calls.Test.storage (address true context_constructor)
      (run true context_constructor 0 [0]) = Some [(0, 0); (1, 13)] /\
    code (address true context_constructor)
      (run true context_constructor 0 [0]) = Some [0].
  Proof. vm_compute. split; reflexivity. Qed.

  Definition context_out_of_gas (opcode : Z) :=
    let state := calls.Test.initial [opcode; 0] [] in
    let interpreter := InstructionContext.State.interpreter _ _ _ state in
    let state : CallFrame.state :=
      {| InstructionContext.State.interpreter := interpreter
           <| @Interpreter.gas WIRE _ WIRE_types _ := Impl_Gas.new 1 |>;
         InstructionContext.State.host := InstructionContext.State.host _ _ _ state |} in
    match CallRunner.run 10 state with
    | Some (InterpreterAction.Return output, final_state) =>
      Some (output.(InterpreterResult.result),
        List.map Uint.value (InstructionContext.State.interpreter _ _ _ final_state)
          .(Interpreter.stack).(Stack.value))
    | _ => None
    end.

  Lemma context_out_of_gas_does_not_push :
    context_out_of_gas 88 = Some (InstructionResult.OutOfGas, []) /\
    context_out_of_gas 56 = Some (InstructionResult.OutOfGas, []).
  Proof. vm_compute. split; reflexivity. Qed.
End Test.
