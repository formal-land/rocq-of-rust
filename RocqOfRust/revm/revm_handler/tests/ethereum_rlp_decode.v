From Stdlib Require Import Bool Lia List ZArith.

Require Import revm.revm_handler.simulate.ethereum_rlp.
Require Import revm.revm_handler.simulate.ethereum_rlp_decode.
Require Import revm.revm_handler.simulate.transaction_auth.

Import ListNotations.
Open Scope Z_scope.

Lemma split_prefix_exact {A : Set} (size : nat) (input : list A) :
  EthereumRlpDecode.split_prefix (Z.of_nat size) input =
    if (size <=? List.length input)%nat then
      Some (List.firstn size input, List.skipn size input)
    else None.
Proof.
  revert size. induction input as [|value tail IH]; intros [|size];
    try reflexivity.
  rewrite Nat2Z.inj_succ.
  cbn [EthereumRlpDecode.split_prefix].
  assert (H_positive : (Z.succ (Z.of_nat size) <=? 0) = false)
    by (apply Z.leb_gt; lia).
  rewrite H_positive.
  replace (Z.succ (Z.of_nat size) - 1) with (Z.of_nat size) by lia.
  rewrite IH. simpl.
  destruct (size <=? List.length tail)%nat; reflexivity.
Qed.

Lemma split_payload_preserves_length_checked_split (size : Z) (input : list Z) :
  EthereumRlpDecode.split_payload size input =
    if (size <? 0) || (Z.of_nat (List.length input) <? size) then None else
    Some (List.firstn (Z.to_nat size) input, List.skipn (Z.to_nat size) input).
Proof.
  unfold EthereumRlpDecode.split_payload.
  destruct (size <? 0) eqn:H_negative; simpl; [reflexivity|].
  apply Z.ltb_ge in H_negative.
  rewrite <- (Z2Nat.id size H_negative) at 1.
  rewrite split_prefix_exact.
  destruct (Z.of_nat (List.length input) <? size) eqn:H_length.
  - apply Z.ltb_lt in H_length.
    assert (H_short : (Z.to_nat size <=? List.length input)%nat = false).
    { apply Nat.leb_gt. lia. }
    rewrite H_short. reflexivity.
  - apply Z.ltb_ge in H_length.
    assert (H_enough : (Z.to_nat size <=? List.length input)%nat = true).
    { apply Nat.leb_le. lia. }
    rewrite H_enough. reflexivity.
Qed.

Module Test.
  Definition nested : EthereumRlp.Item.t := EthereumRlp.Item.List
    [EthereumRlp.Item.Bytes []; EthereumRlp.Item.Bytes [0];
     EthereumRlp.Item.List [EthereumRlp.Item.Bytes [127; 128; 255];
       EthereumRlp.Item.List [EthereumRlp.Item.Bytes [1]]]].

  Lemma canonical_nested_values_round_trip :
    EthereumRlpDecode.decode (EthereumRlp.encode nested) = Some nested.
  Proof. vm_compute. reflexivity. Qed.

  Lemma long_string_and_list_round_trip :
    let items := [EthereumRlp.Item.Bytes (List.repeat 255 56);
      EthereumRlp.Item.List (List.repeat (EthereumRlp.Item.Bytes []) 56)] in
    List.map (fun item => EthereumRlpDecode.decode (EthereumRlp.encode item)) items =
    List.map (@Some EthereumRlp.Item.t) items.
  Proof. vm_compute. reflexivity. Qed.

  Lemma zero_byte_is_a_string_but_not_a_canonical_integer :
    EthereumRlpDecode.decode [0] = Some (EthereumRlp.Item.Bytes [0]) /\
    TransactionAuth.uint (EthereumRlp.Item.Bytes [0]) = None /\
    TransactionAuth.uint (EthereumRlp.Item.Bytes []) = Some 0.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Lemma noncanonical_or_truncated_headers_are_rejected :
    List.map EthereumRlpDecode.decode
      [[]; [129; 0]; [129; 127]; [184; 1; 128]; [184; 0];
       [185; 0; 56]; [248; 1; 128]; [249; 0; 56]; [193]; [194; 129];
       [255; 255; 255; 255; 255; 255; 255; 255; 255]; [128; 128]] =
    List.repeat (@None EthereumRlp.Item.t) 12.
  Proof. vm_compute. reflexivity. Qed.

  Lemma byte_domain_is_checked :
    List.map EthereumRlpDecode.decode [[-1]; [256]; [129; 256]; [193; -1]] =
    List.repeat (@None EthereumRlp.Item.t) 4.
  Proof. vm_compute. reflexivity. Qed.

  Lemma list_children_cannot_cross_the_payload_boundary :
    EthereumRlpDecode.decode [193; 129; 128] = None.
  Proof. vm_compute. reflexivity. Qed.
End Test.
