(** Literal trie vectors are copied from the parent trie/TrieTest.v Geth
    reference vectors. The add11 allocation is the complete canonical native
    transaction output; its expected hash is from the historical fixture.
    All commitment computations in these checks are Rocq definitions. *)
From Stdlib Require Import List ZArith.

Require Import revm.revm_handler.simulate.ethereum_commitment.
Require Import revm.revm_interpreter.tests.stateful_host.

Import ListNotations.
Import EthereumCommitment.
Open Scope Z_scope.

Module Test.
  Lemma trie_empty : Trie.root [] =
  Some ([86;232;31;23;27;204;85;166;255;131;69;230;146;192;248;110;91;72;224;27;153;108;173;192;1;98;47;181;227;99;180;33]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma trie_empty_key : Trie.root [([], [1])] =
  Some ([206;140;75;6;14;150;30;40;90;28;45;106;249;86;250;233;105;134;249;70;16;47;35;183;21;6;82;78;234;158;36;80]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma trie_single : Trie.root [([100;111], [118;101;114;98])] =
  Some ([1;79;7;237;149;226;224;40;128;77;145;94;13;189;78;212;81;227;148;225;172;253;41;228;99;193;26;6;11;45;222;247]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma trie_shared_prefix : Trie.root [([100;111], [118;101;114;98]);
  ([100;111;103], [112;117;112;112;121]);
  ([100;111;103;101], [99;111;105;110;115]);
  ([104;111;114;115;101], [115;116;97;108;108;105;111;110])] =
  Some ([64;52;163;227;25;118;192;132;99;151;10;37;169;181;34;9;191;229;90;229;181;3;0;90;215;122;116;138;43;27;79;81]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma trie_branch_slot_16 : Trie.root [([97], [120]);
  ([97;98], [121])] =
  Some ([215;71;81;247;146;142;75;198;150;203;80;6;255;198;190;9;160;71;98;161;55;24;139;210;84;255;58;93;108;167;171;57]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma trie_inline_boundary_31 : Trie.root [([1], [42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42]);
  ([2], [1])] =
  Some ([71;88;51;212;110;20;32;102;217;95;155;68;247;28;194;32;147;175;177;174;158;188;24;65;21;8;25;203;71;73;98;101]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma trie_hash_boundary_32 : Trie.root [([1], [42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42;42]);
  ([2], [1])] =
  Some ([189;77;89;97;196;83;140;172;6;135;223;239;233;6;240;248;63;12;131;60;68;178;30;161;106;234;215;100;1;222;139;175]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma trie_replace : Trie.root [([97], [120]);
  ([97], [121])] =
  Some ([19;134;67;70;175;167;9;17;251;1;120;250;36;150;231;91;158;97;185;30;151;187;45;137;50;214;16;164;207;77;175;212]).
  Proof. vm_compute. reflexivity. Qed.

  Definition empty_root : list Z :=
    [86;232;31;23;27;204;85;166;255;131;69;230;146;192;248;110;91;72;224;27;153;108;173;192;1;98;47;181;227;99;180;33].

  Lemma empty_storage : storage_root [] = Some empty_root.
  Proof. vm_compute. reflexivity. Qed.

  Lemma zero_storage_values_are_absent :
    storage_root [(1, 0); (2, 0)] = Some empty_root.
  Proof. vm_compute. reflexivity. Qed.

  Lemma duplicate_storage_keys_are_rejected : storage_root [(1, 0); (1, 2)] = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma storage_key_overflow_is_rejected : storage_root [(2 ^ 256, 1)] = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma negative_storage_value_is_rejected : storage_root [(0, -1)] = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_state : state_root [] = Some empty_root.
  Proof. vm_compute. reflexivity. Qed.

  Definition account (address balance nonce : Z) (storage : list (Z * Z)) :
      StatefulHost.Account.t := {|
    StatefulHost.Account.address := address;
    StatefulHost.Account.balance := balance;
    StatefulHost.Account.nonce := nonce;
    StatefulHost.Account.code := [];
    StatefulHost.Account.code_hash := 0;
    StatefulHost.Account.storage := storage;
    StatefulHost.Account.transient_storage := [];
  |}.

  Lemma duplicate_accounts_are_rejected :
    state_root [account 1 0 0 []; account 1 1 0 []] = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma account_address_overflow_is_rejected :
    state_root [account (2 ^ 160) 0 0 []] = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma account_nonce_overflow_is_rejected :
    state_root [account 1 0 (2 ^ 64) []] = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma account_balance_overflow_is_rejected :
    state_root [account 1 (2 ^ 256) 0 []] = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma retained_empty_account_has_presence :
    state_root [account 1 0 0 []] <> Some empty_root.
  Proof. vm_compute. discriminate. Qed.

  Lemma account_order_does_not_change_root :
    state_root [account 1 2 3 [(0, 1)]; account 2 3 4 []] =
    state_root [account 2 3 4 []; account 1 2 3 [(0, 1)]].
  Proof. vm_compute. reflexivity. Qed.

  Lemma storage_order_does_not_change_root :
    storage_root [(1, 2); (3, 4)] = storage_root [(3, 4); (1, 2)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma explicit_zero_slot_does_not_change_root :
    storage_root [(1, 2); (3, 0)] = storage_root [(1, 2)].
  Proof. vm_compute. reflexivity. Qed.

  Definition add11_post_accounts : list StatefulHost.Account.t := [
    {| StatefulHost.Account.address := 53487961227895705414387420465070519070468943239;
       StatefulHost.Account.balance := 1000000000000100000;
       StatefulHost.Account.nonce := 0;
       StatefulHost.Account.code := [96; 1; 96; 1; 1; 96; 0; 85; 0];
       StatefulHost.Account.code_hash := 87753042811415548233916357503970785711690406064839499034040606682585769981253;
       StatefulHost.Account.storage := [(0, 2)];
       StatefulHost.Account.transient_storage := [] |};
    {| StatefulHost.Account.address := 244687034288125203496486448490407391986876152250;
       StatefulHost.Account.balance := 0;
       StatefulHost.Account.nonce := 1;
       StatefulHost.Account.code := [];
       StatefulHost.Account.code_hash := 89477152217924674838424037953991966239322087453347756267410168184682657981552;
       StatefulHost.Account.storage := [];
       StatefulHost.Account.transient_storage := [] |};
    {| StatefulHost.Account.address := 966588469268559010541288244128342317224451555083;
       StatefulHost.Account.balance := 999999999999468880;
       StatefulHost.Account.nonce := 1;
       StatefulHost.Account.code := [];
       StatefulHost.Account.code_hash := 89477152217924674838424037953991966239322087453347756267410168184682657981552;
       StatefulHost.Account.storage := [];
       StatefulHost.Account.transient_storage := [] |}
  ].

  Definition add11_expected_root : list Z :=
    [232; 1; 12; 229; 144; 244; 1; 201; 214; 31; 239; 138; 176; 91; 234; 155; 206; 194; 66; 129; 183; 149; 229; 134; 136; 9; 188; 78; 81; 90; 165; 48].

  Lemma add11_published_post_hash :
    state_root add11_post_accounts = Some add11_expected_root.
  Proof. vm_compute. reflexivity. Qed.

  Lemma add11_account_order_does_not_change_root :
    state_root (List.rev add11_post_accounts) = Some add11_expected_root.
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_logs : logs_hash [] = Some
    [29;204;77;232;222;199;93;122;171;133;181;103;182;204;212;26;211;18;69;27;148;138;116;19;240;161;66;253;64;212;147;71].
  Proof. vm_compute. reflexivity. Qed.

  Lemma nonempty_logs_reference : logs_hash [{|
      StatefulHost.EvmLog.address := 66051;
      StatefulHost.EvmLog.topics := [263430; 11259375];
      StatefulHost.EvmLog.data := [7; 8; 9] |}] = Some
    [12;157;214;69;253;248;213;176;130;250;255;225;180;114;161;94;107;2;221;18;247;32;155;130;100;135;107;238;101;98;98;60].
  Proof. vm_compute. reflexivity. Qed.

  Lemma log_topic_overflow_is_rejected : logs_hash [{|
      StatefulHost.EvmLog.address := 1;
      StatefulHost.EvmLog.topics := [2 ^ 256];
      StatefulHost.EvmLog.data := [] |}] = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma too_many_log_topics_are_rejected : logs_hash [{|
      StatefulHost.EvmLog.address := 1;
      StatefulHost.EvmLog.topics := [1; 2; 3; 4; 5];
      StatefulHost.EvmLog.data := [] |}] = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma log_data_nonbyte_is_rejected : logs_hash [{|
      StatefulHost.EvmLog.address := 1;
      StatefulHost.EvmLog.topics := [];
      StatefulHost.EvmLog.data := [256] |}] = None.
  Proof. vm_compute. reflexivity. Qed.
End Test.
