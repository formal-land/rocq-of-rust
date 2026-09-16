From Stdlib Require Import List ZArith.

Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.bytes.links.mod.
Require Import bytes.links.bytes.
Require Import core.links.result.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.instructions.contract.simulate.account_load.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_primitives.links.hardfork.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Section Host.
    Context (input : StatefulHost.Input.t).

    Definition account (address : Z) (code : list Z) :=
      (StatefulHost.empty_account address)
        <| StatefulHost.Account.code := code |>
        <| StatefulHost.Account.code_hash := address |>.

    Definition load (spec : SpecId.t) (gas : Z) (transfer create : bool)
        (accounts : list StatefulHost.Account.t) (warm : list Z) :=
      let host := List.fold_left StatefulHost.warm_account warm
        (StatefulHost.with_accounts (StatefulHost.make input) accounts) in
      let '(result, host) := account_load.load_account_delegated host spec
        {| Integer.value := gas |} (StatefulHost.rust_address 42) transfer create in
      (match result with
       | Result.Err error => Result.Err error
       | Result.Ok (cost, code, hash) => Result.Ok
           (cost.(Integer.value),
            List.map Integer.value code.(Bytecode.original_bytes)
              .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value),
            FixedBytes.to_Z hash)
       end, host.(StatefulHost.accessed_accounts)).

    Lemma cold_load_reads_actual_code :
      load SpecId.CANCUN 2500 false true [account 42 [96; 7; 0]] [] =
        (Result.Ok (2500, [96; 7; 0], 42), [42]).
    Proof. vm_compute. reflexivity. Qed.

    Lemma warm_load_has_no_additional_charge :
      load SpecId.CANCUN 0 false true [account 42 [96; 7; 0]] [42] =
        (Result.Ok (0, [96; 7; 0], 42), [42]).
    Proof. vm_compute. reflexivity. Qed.

    Lemma skipped_cold_load_does_not_warm :
      load SpecId.CANCUN 2499 false true [account 42 [0]] [] =
        (Result.Err LoadError.ColdLoadSkipped, []).
    Proof. vm_compute. reflexivity. Qed.

    Lemma pre_berlin_has_no_cold_charge :
      load SpecId.ISTANBUL 0 false true [account 42 [0]] [] =
        (Result.Ok (0, [0], 42), [42]).
    Proof. vm_compute. reflexivity. Qed.

    Lemma empty_account_transfer_cost :
      load SpecId.CANCUN 27500 true true [] [] =
        (Result.Ok (27500, [], StatefulHost.empty_code_hash), [42]).
    Proof. vm_compute. reflexivity. Qed.

    Lemma empty_account_without_transfer :
      load SpecId.CANCUN 2500 false true [] [] =
        (Result.Ok (2500, [], StatefulHost.empty_code_hash), [42]).
    Proof. vm_compute. reflexivity. Qed.

    Lemma pre_spurious_empty_account_cost :
      load SpecId.TANGERINE 25000 false true [] [] =
        (Result.Ok (25000, [], StatefulHost.empty_code_hash), [42]).
    Proof. vm_compute. reflexivity. Qed.

    Lemma noncreating_call_does_not_charge_new_account :
      load SpecId.TANGERINE 0 true false [] [] =
        (Result.Ok (0, [], StatefulHost.empty_code_hash), [42]).
    Proof. vm_compute. reflexivity. Qed.

    Definition delegation : list Z := [239; 1; 0] ++ List.repeat 0 19 ++ [43].

    Lemma cold_delegation_loads_one_target :
      load SpecId.PRAGUE 5100 false true
        [account 42 delegation; account 43 [96; 7; 0]] [] =
        (Result.Ok (5100, [96; 7; 0], 43), [43; 42]).
    Proof. vm_compute. reflexivity. Qed.

    Lemma warm_delegation_cost :
      load SpecId.PRAGUE 100 false true
        [account 42 delegation; account 43 [0]] [42; 43] =
        (Result.Ok (100, [0], 43), [43; 42]).
    Proof. vm_compute. reflexivity. Qed.

    Lemma insufficient_delegate_gas_keeps_only_first_warm :
      load SpecId.PRAGUE 5099 false true
        [account 42 delegation; account 43 [0]] [] =
        (Result.Err LoadError.ColdLoadSkipped, [42]).
    Proof. vm_compute. reflexivity. Qed.

    Lemma delegation_is_not_followed_recursively :
      load SpecId.PRAGUE 5100 false true
        [account 42 delegation; account 43 delegation] [] =
        (Result.Ok (5100, delegation, 43), [43; 42]).
    Proof. vm_compute. reflexivity. Qed.
  End Host.
End Test.
