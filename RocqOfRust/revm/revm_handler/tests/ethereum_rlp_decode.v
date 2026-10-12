From Stdlib Require Import List ZArith.

Require Import revm.revm_handler.simulate.ethereum_rlp.
Require Import revm.revm_handler.simulate.ethereum_rlp_decode.
Require Import revm.revm_handler.simulate.transaction_auth.

Import ListNotations.
Open Scope Z_scope.

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
