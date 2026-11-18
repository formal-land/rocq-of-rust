From Stdlib Require Import List ZArith.
Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.bits.simulate.address_creation.
Require Import alloy_primitives.utils.simulate.keccak256.
Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition caller : Address.t :=
    {| Address.value := 1271270612704050900734399246419756505046821371904 |}.

  Definition create2 (code : list Z) : Z :=
    let hash := FixedBytes.from_Z
      (List.fold_left (fun value byte => 256 * value + byte) (Keccak256.hash code) 0) in
    (Impl_AddressCreation.create2 {| Address.value := 0 |} (FixedBytes.from_Z 0) hash).(Address.value).

  (* Independent RLP/Keccak vectors, including both nonce encoding boundaries. *)
  Lemma nonce_boundaries :
    List.map (fun nonce =>
      (Impl_AddressCreation.create caller {| Integer.value := nonce |}).(Address.value)) [0; 1; 127; 128; 255; 256; 18446744073709551615] =
    [1381677183835197397371320389193835251383183634154;
       30281032363418399476905464504919735214508311185;
       730283248267334925037332234392401136189879599150;
       197483594112168445870481239125977973709724759308;
       1146469685200992900227744465822269831875523790341;
       918388382260733050713788283349437782974347981187;
       587518049645600016083424227496294937513719939365].
  Proof. vm_compute. reflexivity. Qed.

  Lemma create2_zero_byte :
    create2 [0] = 440176130766443707569614712219969213191074266936.
  Proof. vm_compute. reflexivity. Qed.

  Lemma create2_empty_code :
    create2 [] = 1297280038419638216961985153415887283996015188448.
  Proof. vm_compute. reflexivity. Qed.

End Test.
