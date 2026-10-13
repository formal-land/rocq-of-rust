From Stdlib Require Import List ZArith.

Require Import revm.revm_handler.simulate.handler.
Require Import revm.revm_interpreter.tests.stateful_dispatch.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition designation (address : Z) := [239; 1; 0] ++ List.repeat 0 19 ++ [address].

  Definition account (address : Z) (code : list Z) :=
    (StatefulHost.empty_account address) <| StatefulHost.Account.code := code |>.

  Definition host (accounts : list StatefulHost.Account.t) :=
    StatefulHost.warm_account
      (StatefulHost.make (add11_input <| StatefulHost.Input.state := accounts |>)) 42.

  Lemma first_frame_resolves_delegate :
    fst (handler.first_frame_input 42
      (host [account 42 (designation 43); account 43 [48; 0]])) = [48; 0].
  Proof. vm_compute. reflexivity. Qed.

  Lemma first_frame_warms_delegate :
    StatefulHost.account_is_warm (snd (handler.first_frame_input 42
      (host [account 42 (designation 43); account 43 [0]]))) 43 = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma first_frame_resolves_only_one_level :
    fst (handler.first_frame_input 42
      (host [account 42 (designation 43); account 43 (designation 44);
        account 44 [0]])) = designation 44.
  Proof. vm_compute. reflexivity. Qed.

  Lemma first_frame_does_not_warm_second_delegate :
    StatefulHost.account_is_warm (snd (handler.first_frame_input 42
      (host [account 42 (designation 43); account 43 (designation 44);
        account 44 [0]]))) 44 = false.
  Proof. vm_compute. reflexivity. Qed.

  Lemma first_frame_missing_delegate_is_empty :
    fst (handler.first_frame_input 42 (host [account 42 (designation 43)])) = [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma first_frame_short_designation_is_legacy :
    fst (handler.first_frame_input 42 (host [account 42 [239; 1; 0; 43]])) =
      [239; 1; 0; 43].
  Proof. vm_compute. reflexivity. Qed.

  Lemma first_frame_delegate_precompile_loads_empty_code :
    fst (handler.first_frame_input 42 (host [account 42 (designation 2)])) = [].
  Proof. vm_compute. reflexivity. Qed.

  Lemma first_frame_preserves_authority_code :
    option_map StatefulHost.Account.code
      (StatefulHost.find_account 42 (snd (handler.first_frame_input 42
        (host [account 42 (designation 43); account 43 [0]]))).(StatefulHost.accounts)) =
      Some (designation 43).
  Proof. vm_compute. reflexivity. Qed.

  Lemma first_frame_warms_original_target :
    StatefulHost.account_is_warm (snd (handler.first_frame_input 43
      (host [account 43 [0]]))) 43 = true.
  Proof. vm_compute. reflexivity. Qed.
End Test.
