From Stdlib Require Import Bool List ZArith.

Require Import alloy_primitives.utils.simulate.keccak256.

Import ListNotations.
Open Scope Z_scope.

Module CreateAddress.
  Definition big_endian (width : nat) (value : Z) : list Z :=
    List.map (fun index =>
      Z.land (Z.shiftr value (8 * Z.of_nat (width - S index))) 255)
      (List.seq 0 width).

  Definition hash_address (input : list Z) : Z :=
    List.fold_left (fun value byte => 256 * value + byte)
      (List.skipn 12 (Keccak256.hash input)) 0.

  Definition create (caller nonce : Z) : option Z :=
    if (0 <=? caller) && (caller <? 2 ^ 160) &&
       (0 <=? nonce) && (nonce <? 2 ^ 64) then
      let nonce_bytes :=
        if nonce =? 0 then [128]
        else if nonce <? 128 then [nonce]
        else
          let width := Z.to_nat ((Z.log2 nonce + 8) / 8) in
          (128 + Z.of_nat width) :: big_endian width nonce in
      let payload := 148 :: big_endian 20 caller ++ nonce_bytes in
      Some (hash_address ((192 + Z.of_nat (List.length payload)) :: payload))
    else None.

  Definition create2 (caller salt : Z) (init_code : list Z) : option Z :=
    if (0 <=? caller) && (caller <? 2 ^ 160) &&
       (0 <=? salt) && (salt <? 2 ^ 256) &&
       List.forallb (fun byte => (0 <=? byte) && (byte <? 256)) init_code then
      Some (hash_address
        (255 :: big_endian 20 caller ++ big_endian 32 salt ++ Keccak256.hash init_code))
    else None.

  Module Test.
    Definition caller : Z := 1271270612704050900734399246419756505046821371904.

    (* Independent RLP/Keccak vectors, including both nonce encoding boundaries. *)
    Lemma nonce_boundaries :
      List.map (create caller) [0; 1; 127; 128; 255; 256; 18446744073709551615] =
      List.map (@Some Z)
        [1381677183835197397371320389193835251383183634154;
         30281032363418399476905464504919735214508311185;
         730283248267334925037332234392401136189879599150;
         197483594112168445870481239125977973709724759308;
         1146469685200992900227744465822269831875523790341;
         918388382260733050713788283349437782974347981187;
         587518049645600016083424227496294937513719939365].
    Proof. vm_compute. reflexivity. Qed.

    Lemma create2_zero_byte :
      create2 0 0 [0] = Some 440176130766443707569614712219969213191074266936.
    Proof. vm_compute. reflexivity. Qed.

    Lemma create2_empty_code :
      create2 0 0 [] = Some 1297280038419638216961985153415887283996015188448.
    Proof. vm_compute. reflexivity. Qed.

    Lemma invalid_nonce :
      create caller (-1) = None /\ create caller (2 ^ 64) = None.
    Proof. vm_compute. split; reflexivity. Qed.

    Lemma invalid_create2_input :
      create2 0 (2 ^ 256) [] = None /\ create2 0 0 [256] = None.
    Proof. vm_compute. split; reflexivity. Qed.
  End Test.
End CreateAddress.
