From Stdlib Require Import List ZArith.

Require Import revm.revm_handler.simulate.ethereum_rlp.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Lemma empty_bytes : EthereumRlp.encode_bytes [] = [128].
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_list : EthereumRlp.encode_list [] = [192].
  Proof. vm_compute. reflexivity. Qed.

  Lemma singleton_127 : EthereumRlp.encode_bytes [127] = [127].
  Proof. vm_compute. reflexivity. Qed.

  Lemma singleton_128 : EthereumRlp.encode_bytes [128] = [129; 128].
  Proof. vm_compute. reflexivity. Qed.

  Lemma short_bytes_limit :
    EthereumRlp.encode_bytes (List.repeat 42 55) = 183 :: List.repeat 42 55.
  Proof. vm_compute. reflexivity. Qed.

  Lemma long_bytes_start :
    EthereumRlp.encode_bytes (List.repeat 42 56) = 184 :: 56 :: List.repeat 42 56.
  Proof. vm_compute. reflexivity. Qed.

  Lemma short_list_limit :
    EthereumRlp.encode_list [List.repeat 42 55] = 247 :: List.repeat 42 55.
  Proof. vm_compute. reflexivity. Qed.

  Lemma long_list_start :
    EthereumRlp.encode_list [List.repeat 42 56] = 248 :: 56 :: List.repeat 42 56.
  Proof. vm_compute. reflexivity. Qed.

  Lemma two_byte_length :
    EthereumRlp.encode_bytes (List.repeat 42 256) = 185 :: 1 :: 0 :: List.repeat 42 256.
  Proof. vm_compute. reflexivity. Qed.

  Lemma zero_uint : EthereumRlp.encode_uint 0 = [128].
  Proof. vm_compute. reflexivity. Qed.

  Lemma multi_byte_uint : EthereumRlp.encode_uint 1024 = [130; 4; 0].
  Proof. vm_compute. reflexivity. Qed.

  Lemma fixed_width_padding : EthereumRlp.fixed_big_endian 4 258 = [0; 0; 1; 2].
  Proof. vm_compute. reflexivity. Qed.

  Lemma nested_list :
    EthereumRlp.encode (EthereumRlp.Item.List [
      EthereumRlp.Item.Bytes [99; 97; 116];
      EthereumRlp.Item.List [EthereumRlp.Item.Bytes []; EthereumRlp.Item.Bytes [1]]]) =
    [199; 131; 99; 97; 116; 194; 128; 1].
  Proof. vm_compute. reflexivity. Qed.
End Test.
