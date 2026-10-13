From Stdlib Require Import List ZArith.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_context_interface.links.host.
Require Import core.links.result.
Require Import revm.revm_interpreter.instructions.contract.simulate.account_load.
Require Import revm.revm_interpreter.tests.calls.
Require Import revm.revm_interpreter.tests.stateful_dispatch.
Require Import simulate.RocqOfRust.
Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition designation (address : Z) := [239; 1; 0] ++ List.repeat 0 19 ++ [address].

  Definition state := InstructionContext.State.host _ _ _
    (calls.Test.initial [] (designation 44)).

  Definition load (gas : Z) (host : StatefulHost.t) :=
    account_load.load_account_delegated host SpecId.OSAKA
      (gas : u64) (StatefulHost.rust_address 43) false true.

  Definition cost (result : Result.t (u64 * revm.revm_bytecode.links.bytecode.Bytecode.t * aliases.B256.t) LoadError.t * StatefulHost.t) :=
    match fst result with
    | Result.Ok (cost, _, _) => Some cost.(Integer.value)
    | _ => None
    end.

  Lemma cold_authority_and_delegate_cost : cost (load 5100 state) = Some 5100.
  Proof. vm_compute. reflexivity. Qed.

  Lemma insufficient_delegate_gas : cost (load 5099 state) = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma failed_delegate_load_keeps_delegate_cold :
    StatefulHost.account_is_warm (snd (load 5099 state)) 44 = false.
  Proof. vm_compute. reflexivity. Qed.

  Lemma failed_delegate_load_warms_authority :
    StatefulHost.account_is_warm (snd (load 5099 state)) 43 = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma warm_authority_cold_delegate_cost :
    cost (load 2600 (StatefulHost.warm_account state 43)) = Some 2600.
  Proof. vm_compute. reflexivity. Qed.

  Lemma both_warm_cost :
    cost (load 100 (StatefulHost.warm_account (StatefulHost.warm_account state 43) 44)) = Some 100.
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegation_call_writes_authority_storage :
    calls.Test.storage 43 (calls.Test.run (calls.Test.call 0 0 0 50000 ++ [0])
      (designation 44)) = Some [(0,9)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegation_call_does_not_write_delegate_storage :
    calls.Test.storage 44 (calls.Test.run (calls.Test.call 0 0 0 50000 ++ [0])
      (designation 44)) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegation_callcode_writes_parent_storage :
    calls.Test.storage 42 (calls.Test.run ([96; 0; 96; 0; 96; 0; 96; 0; 96; 0; 96; 43; 98; 1; 17; 112; 242] ++ [0])
      (designation 44)) = Some [(0,9)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegation_delegatecall_writes_parent_storage :
    calls.Test.storage 42 (calls.Test.run ([96; 0; 96; 0; 96; 0; 96; 0; 96; 43; 98; 1; 17; 112; 244] ++ [0])
      (designation 44)) = Some [(0,9)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegation_staticcall_rejects_storage_write :
    calls.Test.stack (calls.Test.run
      ([96; 0; 96; 0; 96; 0; 96; 0; 96; 43; 97; 195; 80; 250; 0])
      (designation 44)) = Some [0].
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegation_to_precompile_does_not_execute_precompile :
    calls.Test.stack (calls.Test.run (calls.Test.call 0 0 0 0 ++ [0])
      (designation 2)) = Some [1].
  Proof. vm_compute. reflexivity. Qed.

  Lemma delegation_to_self_is_not_recursively_resolved :
    calls.Test.stack (calls.Test.run (calls.Test.call 0 0 0 50000 ++ [0])
      (designation 43)) = Some [0].
  Proof. vm_compute. reflexivity. Qed.
End Test.
