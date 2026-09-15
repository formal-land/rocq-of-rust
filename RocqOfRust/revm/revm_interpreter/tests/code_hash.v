From Stdlib Require Import List ZArith.

Require Import revm.revm_interpreter.instructions.simulate.host.extcodehash.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Section Input.
    Context (input : StatefulHost.Input.t).

    Definition empty_code_hash : Z :=
      89477152217924674838424037953991966239322087453347756267410168184682657981552.

    Definition account (balance nonce hash : Z) : StatefulHost.Account.t := {|
      StatefulHost.Account.address := 42;
      StatefulHost.Account.balance := balance;
      StatefulHost.Account.nonce := nonce;
      StatefulHost.Account.code := [];
      StatefulHost.Account.code_hash := hash;
      StatefulHost.Account.storage := [];
      StatefulHost.Account.transient_storage := [];
    |}.

    Definition run_hash (spec : SpecId.t) (gas_limit : Z)
        (accounts : list StatefulHost.Account.t) (args warm : list Z) :=
      let interpreter : Interpreter.t WIRE WIRE_types :=
        (make_interpreter {| Stack.value := List.map (fun x => {| Uint.value := x |}) args |})
          <| @Interpreter.runtime_flag WIRE _ WIRE_types _ := spec |> in
      let interpreter : Interpreter.t WIRE WIRE_types :=
        interpreter <| @Interpreter.gas WIRE _ WIRE_types _ :=
          interpreter.(Interpreter.gas)
            <| Gas.limit := {| Integer.value := gas_limit |} |>
            <| Gas.remaining := {| Integer.value := gas_limit |} |> |> in
      let host := List.fold_left StatefulHost.warm_account warm
        (StatefulHost.with_accounts (StatefulHost.make input) accounts) in
      let '(interpreter, host) := extcodehash interpreter host in
      (List.map Uint.value interpreter.(Interpreter.stack).(Stack.value),
       interpreter.(Interpreter.gas).(Gas.remaining).(Integer.value),
       host.(StatefulHost.accessed_accounts),
       match interpreter.(Interpreter.bytecode).(Bytecode.action) with
       | Some (InterpreterAction.Return result) => Some result.(InterpreterResult.result)
       | _ => None
       end).

    Lemma absent_account_returns_zero :
      run_hash SpecId.CANCUN 3000 [] [42] [] = ([0], 400, [42], None).
    Proof. vm_compute. reflexivity. Qed.

    Lemma empty_account_returns_zero :
      run_hash SpecId.CANCUN 3000 [account 0 0 empty_code_hash] [42] [] =
      ([0], 400, [42], None).
    Proof. vm_compute. reflexivity. Qed.

    Lemma funded_account_without_code_returns_empty_hash :
      run_hash SpecId.CANCUN 3000 [account 1 0 empty_code_hash] [42] [] =
      ([empty_code_hash], 400, [42], None).
    Proof. vm_compute. reflexivity. Qed.

    Lemma nonzero_nonce_without_code_returns_empty_hash :
      run_hash SpecId.CANCUN 3000 [account 0 1 empty_code_hash] [42] [] =
      ([empty_code_hash], 400, [42], None).
    Proof. vm_compute. reflexivity. Qed.

    Lemma warm_access_costs_100 :
      run_hash SpecId.CANCUN 100 [account 1 0 empty_code_hash] [42] [42] =
      ([empty_code_hash], 0, [42], None).
    Proof. vm_compute. reflexivity. Qed.

    Lemma insufficient_cold_gas_does_not_load_account :
      run_hash SpecId.CANCUN 2599 [] [42] [] =
      ([42], 0, [], Some InstructionResult.OutOfGas).
    Proof. vm_compute. reflexivity. Qed.

    Lemma constantinople_costs_400 :
      run_hash SpecId.CONSTANTINOPLE 400 [account 1 0 empty_code_hash] [42] [] =
      ([empty_code_hash], 0, [42], None).
    Proof. vm_compute. reflexivity. Qed.

    Lemma istanbul_costs_700 :
      run_hash SpecId.ISTANBUL 700 [account 1 0 empty_code_hash] [42] [] =
      ([empty_code_hash], 0, [42], None).
    Proof. vm_compute. reflexivity. Qed.

    Lemma unavailable_before_constantinople :
      run_hash SpecId.BYZANTIUM 3000 [] [42] [] =
      ([42], 3000, [], Some InstructionResult.NotActivated).
    Proof. vm_compute. reflexivity. Qed.

    Lemma stack_underflow_does_not_load_account :
      run_hash SpecId.CANCUN 3000 [] [] [] =
      ([], 3000, [], Some InstructionResult.StackUnderflow).
    Proof. vm_compute. reflexivity. Qed.

    Lemma address_is_truncated_to_160_bits :
      run_hash SpecId.CANCUN 2600 [account 1 0 empty_code_hash]
        [2 ^ 160 + 42] [] = ([empty_code_hash], 0, [42], None).
    Proof. vm_compute. reflexivity. Qed.

    Lemma insufficient_base_gas_does_not_load_account :
      run_hash SpecId.CANCUN 99 [] [42] [] =
      ([42], 0, [], Some InstructionResult.OutOfGas).
    Proof. vm_compute. reflexivity. Qed.

    Lemma zero_hash_empty_account_returns_zero :
      run_hash SpecId.CANCUN 2600 [account 0 0 0] [42] [] =
      ([0], 0, [42], None).
    Proof. vm_compute. reflexivity. Qed.
  End Input.
End Test.
