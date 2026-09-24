From Stdlib Require Import List ZArith.

Require Import alloy_primitives.utils.simulate.keccak256.
Require Import revm.revm_interpreter.tests.create_address.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module LogObservation.
  Definition length_prefix (base : Z) (payload : list Z) : list Z :=
    let size := Z.of_nat (List.length payload) in
    if size <? 56 then (base + size) :: payload
    else
      let width := Z.to_nat ((Z.log2 size + 8) / 8) in
      (base + 55 + Z.of_nat width) :: CreateAddress.big_endian width size ++ payload.

  Definition encode_bytes (data : list Z) : list Z :=
    match data with
    | [byte] => if byte <? 128 then data else length_prefix 128 data
    | _ => length_prefix 128 data
    end.

  Definition encode_log (entry : StatefulHost.EvmLog.t) : list Z :=
    length_prefix 192
      (encode_bytes (CreateAddress.big_endian 20 entry.(StatefulHost.EvmLog.address)) ++
       length_prefix 192 (List.flat_map
         (fun topic => encode_bytes (CreateAddress.big_endian 32 topic))
         entry.(StatefulHost.EvmLog.topics)) ++
       encode_bytes entry.(StatefulHost.EvmLog.data)).

  Definition encode (logs : list StatefulHost.EvmLog.t) : list Z :=
    length_prefix 192 (List.flat_map encode_log logs).

  Definition hash (logs : list StatefulHost.EvmLog.t) : Z :=
    List.fold_left (fun value byte => 256 * value + byte)
      (Keccak256.hash (encode logs)) 0.

  Module Test.
    Definition entry : StatefulHost.EvmLog.t :=
      {| StatefulHost.EvmLog.address := 42;
         StatefulHost.EvmLog.topics := [1; 2];
         StatefulHost.EvmLog.data := [42] |}.

    Lemma empty_log_list :
      encode [] = [192] /\
      hash [] = 13478047122767188135818125966132228187941283477090363246179690878162135454535.
    Proof. vm_compute. split; reflexivity. Qed.

    Lemma log_hash_vector :
      hash [entry] = 62968268295090227926899696341152952853786106178775180983160742702712912081193.
    Proof. vm_compute. reflexivity. Qed.

    Lemma byte_string_boundaries :
      encode_bytes [] = [128] /\ encode_bytes [0] = [0] /\
      encode_bytes [127] = [127] /\ encode_bytes [128] = [129; 128] /\
      encode_bytes (List.repeat 1 55) = 183 :: List.repeat 1 55 /\
      encode_bytes (List.repeat 1 56) = [184; 56] ++ List.repeat 1 56 /\
      encode_bytes (List.repeat 1 256) = [185; 1; 0] ++ List.repeat 1 256.
    Proof. vm_compute. repeat split; reflexivity. Qed.

    Lemma list_boundaries :
      length_prefix 192 (List.repeat 1 55) = 247 :: List.repeat 1 55 /\
      length_prefix 192 (List.repeat 1 56) = [248; 56] ++ List.repeat 1 56.
    Proof. vm_compute. split; reflexivity. Qed.

    Lemma fields_and_order_are_observable :
      encode [entry] <>
        encode [entry <| StatefulHost.EvmLog.address := 43 |>] /\
      encode [entry] <>
        encode [entry <| StatefulHost.EvmLog.topics := [2; 1] |>] /\
      encode [entry] <>
        encode [entry <| StatefulHost.EvmLog.data := [43] |>] /\
      encode [entry] <> encode [] /\
      encode [entry] <> encode [entry; entry].
    Proof. vm_compute. repeat split; discriminate. Qed.
  End Test.
End LogObservation.
