From Stdlib Require Import Bool List ZArith.

Require Import revm.revm_handler.simulate.ethereum_rlp.
Require Import revm.revm_handler.simulate.ethereum_rlp_decode.
Require Import revm.revm_handler.simulate.transaction_accounting.
Require Import revm.revm_handler.simulate.transaction_auth.
Require Import revm.revm_precompile.simulate.secp256k1.
Require Import revm.revm_primitives.links.hardfork.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition sender (result : TransactionAuth.Result.t) : option Z :=
    match result with
    | TransactionAuth.Result.Authenticated tx => Some tx.(TransactionAccounting.Transaction.caller)
    | _ => None
    end.

  Definition decoded_hash (raw : list Z) : option Z :=
    match TransactionAuth.decode raw with
    | TransactionAuth.DecodeResult.Decoded envelope => Some (TransactionAuth.signing_hash envelope)
    | _ => None
    end.

  Definition rewrite_field (tx_type : Z) (input : list Z) (index : nat)
      (replacement : EthereumRlp.Item.t) : list Z :=
    match EthereumRlpDecode.decode (if tx_type =? 0 then input else List.skipn 1 input) with
    | Some (EthereumRlp.Item.List fields) =>
        (if tx_type =? 0 then [] else [tx_type]) ++ EthereumRlp.encode
          (EthereumRlp.Item.List
            (List.firstn index fields ++ [replacement] ++ List.skipn (S index) fields))
    | _ => []
    end.

  Definition uint_item (value : Z) := EthereumRlp.Item.Bytes (EthereumRlp.big_endian value).

  (* GeneralStateTests/stExample/add11.json; SHA256 ce5a21a1b744ae982aef4fee0d41c1746fb77cf2182059d005901d64502700da. *)
  Definition add11_raw : list Z :=
    [248; 99; 128; 10; 131; 6; 26; 128; 148; 9; 94; 123; 174; 166; 166; 199; 196; 194; 223; 235; 151; 126; 250; 195; 38; 175; 85; 45; 135; 131; 1; 134; 160; 128; 27; 160; 255; 182; 0; 230; 49; 21; 167; 54; 46; 120; 17; 137; 74; 145; 216; 186; 67; 48; 229; 38; 242; 33; 33; 201; 148; 196; 105; 32; 53; 223; 223; 213; 160; 97; 152; 55; 159; 202; 200; 222; 61; 191; 172; 72; 177; 101; 223; 75; 248; 142; 32; 136; 242; 148; 182; 30; 251; 154; 101; 254; 34; 129; 199; 110; 22].

  Lemma add11_authenticates_every_normalized_field :
    TransactionAuth.authenticate 1 (Some 966588469268559010541288244128342317224451555083) add11_raw =
    TransactionAuth.Result.Authenticated {| TransactionAccounting.Transaction.tx_type := 0;
       TransactionAccounting.Transaction.caller := 966588469268559010541288244128342317224451555083;
       TransactionAccounting.Transaction.target := (Some 53487961227895705414387420465070519070468943239);
       TransactionAccounting.Transaction.nonce := 0;
       TransactionAccounting.Transaction.chain_id := None;
       TransactionAccounting.Transaction.gas_limit := 400000;
       TransactionAccounting.Transaction.gas_price := 10;
       TransactionAccounting.Transaction.max_priority_fee := None;
       TransactionAccounting.Transaction.access_list := [];
       TransactionAccounting.Transaction.max_fee_per_blob_gas := 0;
       TransactionAccounting.Transaction.blob_hashes := [];
       TransactionAccounting.Transaction.value := 100000;
       TransactionAccounting.Transaction.data := [];
       TransactionAccounting.Transaction.authorization_list := []; |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma add11_signing_hash_matches_independent_reference :
    decoded_hash add11_raw = Some 15024008012907054605950825217935212414626899601004337329052610295012914367147.
  Proof. vm_compute. reflexivity. Qed.

  (* GeneralStateTests/stExample/accessListExample.json; SHA256 13786ad3123bc96e9f62359fc2e035f57e9cb7bc82fccfea25904f16e451c3dc. *)
  Definition access_list_raw : list Z :=
    [1; 248; 249; 1; 128; 10; 131; 6; 26; 128; 148; 9; 94; 123; 174; 166; 166; 199; 196; 194; 223; 235; 151; 126; 250; 195; 38; 175; 85; 45; 135; 131; 1; 134; 160; 0; 248; 147; 248; 89; 148; 9; 94; 123; 174; 166; 166; 199; 196; 194; 223; 235; 151; 126; 250; 195; 38; 175; 85; 45; 135; 248; 66; 160; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 160; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 247; 148; 25; 94; 123; 174; 166; 166; 199; 196; 194; 223; 235; 151; 126; 250; 195; 38; 175; 85; 45; 135; 225; 160; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 128; 160; 17; 201; 126; 11; 184; 163; 86; 254; 79; 73; 179; 120; 99; 208; 89; 198; 254; 140; 211; 33; 74; 106; 192; 106; 131; 135; 162; 246; 240; 183; 95; 96; 160; 33; 35; 104; 161; 9; 125; 163; 8; 6; 237; 253; 19; 217; 195; 86; 98; 225; 186; 238; 147; 146; 53; 235; 37; 222; 134; 121; 128; 189; 14; 218; 38].

  Lemma access_list_authenticates_every_normalized_field :
    TransactionAuth.authenticate 1 (Some 966588469268559010541288244128342317224451555083) access_list_raw =
    TransactionAuth.Result.Authenticated {| TransactionAccounting.Transaction.tx_type := 1;
       TransactionAccounting.Transaction.caller := 966588469268559010541288244128342317224451555083;
       TransactionAccounting.Transaction.target := (Some 53487961227895705414387420465070519070468943239);
       TransactionAccounting.Transaction.nonce := 0;
       TransactionAccounting.Transaction.chain_id := (Some 1);
       TransactionAccounting.Transaction.gas_limit := 400000;
       TransactionAccounting.Transaction.gas_price := 10;
       TransactionAccounting.Transaction.max_priority_fee := None;
       TransactionAccounting.Transaction.access_list := [(53487961227895705414387420465070519070468943239, [0; 1]); (144831813561077137802117722509838207798964727175, [0])];
       TransactionAccounting.Transaction.max_fee_per_blob_gas := 0;
       TransactionAccounting.Transaction.blob_hashes := [];
       TransactionAccounting.Transaction.value := 100000;
       TransactionAccounting.Transaction.data := [0];
       TransactionAccounting.Transaction.authorization_list := []; |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma access_list_signing_hash_matches_independent_reference :
    decoded_hash access_list_raw = Some 66426445379298571151804860922215095327808521460965102408825684973186593404949.
  Proof. vm_compute. reflexivity. Qed.

  (* GeneralStateTests/stExample/eip1559.json; SHA256 826e2d4d70e554a2404e73bee93857674ecc12e8db4deb31189accb5a2b2d085. *)
  Definition dynamic_fee_raw : list Z :=
    [2; 248; 193; 1; 1; 10; 130; 7; 208; 131; 61; 9; 0; 148; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 128; 0; 248; 91; 248; 89; 148; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 204; 248; 66; 160; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 160; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 128; 160; 214; 113; 129; 88; 152; 184; 221; 52; 50; 26; 219; 186; 76; 182; 165; 123; 170; 112; 23; 50; 60; 38; 148; 111; 55; 25; 176; 14; 112; 199; 85; 194; 160; 53; 40; 185; 239; 227; 190; 87; 234; 101; 169; 51; 209; 230; 187; 243; 183; 208; 199; 136; 48; 19; 136; 131; 193; 32; 30; 12; 100; 31; 238; 100; 100].

  Lemma dynamic_fee_authenticates_every_normalized_field :
    TransactionAuth.authenticate 1 (Some 966588469268559010541288244128342317224451555083) dynamic_fee_raw =
    TransactionAuth.Result.Authenticated {| TransactionAccounting.Transaction.tx_type := 2;
       TransactionAccounting.Transaction.caller := 966588469268559010541288244128342317224451555083;
       TransactionAccounting.Transaction.target := (Some 1169201309864722334562947866173026415724746034380);
       TransactionAccounting.Transaction.nonce := 1;
       TransactionAccounting.Transaction.chain_id := (Some 1);
       TransactionAccounting.Transaction.gas_limit := 4000000;
       TransactionAccounting.Transaction.gas_price := 2000;
       TransactionAccounting.Transaction.max_priority_fee := (Some 10);
       TransactionAccounting.Transaction.access_list := [(1169201309864722334562947866173026415724746034380, [0; 1])];
       TransactionAccounting.Transaction.max_fee_per_blob_gas := 0;
       TransactionAccounting.Transaction.blob_hashes := [];
       TransactionAccounting.Transaction.value := 0;
       TransactionAccounting.Transaction.data := [0];
       TransactionAccounting.Transaction.authorization_list := []; |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_fee_signing_hash_matches_independent_reference :
    decoded_hash dynamic_fee_raw = Some 354466888644641162156156018052683070530725835528408928053321929178166172968.
  Proof. vm_compute. reflexivity. Qed.

  (* GeneralStateTests/Cancun/stEIP4844-blobtransactions/opcodeBlobhashOutOfRange.json; SHA256 5e94d2568ca105d3cdd8ac6b3ac1552d9c559c97c11c4f604733c40c06e423db. *)
  Definition blob_raw : list Z :=
    [3; 249; 1; 12; 1; 128; 2; 133; 1; 42; 5; 242; 0; 131; 61; 9; 0; 148; 9; 94; 123; 174; 166; 166; 199; 196; 194; 223; 235; 151; 126; 250; 195; 38; 175; 85; 45; 135; 131; 1; 134; 160; 0; 248; 91; 248; 89; 148; 9; 94; 123; 174; 166; 166; 199; 196; 194; 223; 235; 151; 126; 250; 195; 38; 175; 85; 45; 135; 248; 66; 160; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 160; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 10; 248; 66; 160; 1; 169; 21; 228; 208; 96; 20; 158; 180; 54; 89; 96; 230; 167; 164; 95; 51; 67; 147; 9; 48; 97; 17; 107; 25; 126; 50; 64; 6; 95; 242; 216; 160; 1; 169; 21; 228; 208; 96; 20; 158; 180; 54; 89; 96; 230; 167; 164; 95; 51; 67; 147; 9; 48; 97; 17; 107; 25; 126; 50; 64; 6; 95; 242; 216; 128; 160; 191; 117; 30; 213; 195; 123; 214; 93; 58; 206; 91; 115; 161; 198; 47; 115; 136; 178; 3; 168; 44; 227; 102; 57; 46; 123; 118; 253; 45; 225; 44; 177; 160; 111; 43; 83; 68; 229; 185; 151; 211; 91; 58; 7; 104; 0; 97; 150; 166; 92; 78; 255; 142; 211; 172; 173; 82; 1; 161; 5; 194; 181; 155; 78; 140].

  Lemma blob_authenticates_every_normalized_field :
    TransactionAuth.authenticate 1 (Some 966588469268559010541288244128342317224451555083) blob_raw =
    TransactionAuth.Result.Authenticated {| TransactionAccounting.Transaction.tx_type := 3;
       TransactionAccounting.Transaction.caller := 966588469268559010541288244128342317224451555083;
       TransactionAccounting.Transaction.target := (Some 53487961227895705414387420465070519070468943239);
       TransactionAccounting.Transaction.nonce := 0;
       TransactionAccounting.Transaction.chain_id := (Some 1);
       TransactionAccounting.Transaction.gas_limit := 4000000;
       TransactionAccounting.Transaction.gas_price := 5000000000;
       TransactionAccounting.Transaction.max_priority_fee := (Some 2);
       TransactionAccounting.Transaction.access_list := [(53487961227895705414387420465070519070468943239, [0; 1])];
       TransactionAccounting.Transaction.max_fee_per_blob_gas := 10;
       TransactionAccounting.Transaction.blob_hashes := [751061108016417963655666671466479409693641967685740960873602276217728266968; 751061108016417963655666671466479409693641967685740960873602276217728266968];
       TransactionAccounting.Transaction.value := 100000;
       TransactionAccounting.Transaction.data := [0];
       TransactionAccounting.Transaction.authorization_list := []; |}.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_signing_hash_matches_independent_reference :
    decoded_hash blob_raw = Some 53464110527347784046739797375672791322553035786353690874850992018156419996145.
  Proof. vm_compute. reflexivity. Qed.

  (* TransactionTests/ttSignature/invalidSignature.json; SHA256 0063434078c3093d5f8272ec7a71a269782a038861af83e94f2eca3340510cdc. *)
  Definition invalid_r_raw : list Z := [248; 99; 128; 128; 131; 15; 66; 64; 148; 9; 94; 123; 174; 166; 166; 199; 196; 194; 223; 235; 151; 126; 250; 195; 38; 175; 85; 45; 135; 131; 1; 134; 160; 128; 27; 160; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 160; 186; 223; 0; 215; 14; 194; 140; 148; 163; 181; 94; 199; 113; 188; 188; 112; 119; 141; 110; 224; 181; 28; 167; 234; 149; 20; 89; 76; 134; 27; 24; 132].

  Lemma native_fixture_invalid_r_is_rejected :
    TransactionAuth.authenticate 1 None invalid_r_raw =
    TransactionAuth.Result.Rejected TransactionAuth.Error.InvalidSignature.
  Proof. vm_compute. reflexivity. Qed.

  (* TransactionTests/ttSignature/RSsecp256k1.json; SHA256 d72bd5aa1a311c1b8a502cacb85017f434409d93afae1f38349c22c23d5d8080. *)
  Definition invalid_r_and_s_raw : list Z := [248; 95; 3; 1; 130; 82; 8; 148; 185; 79; 83; 116; 252; 229; 237; 188; 142; 42; 134; 151; 193; 83; 49; 103; 126; 110; 191; 11; 10; 128; 28; 160; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 254; 186; 174; 220; 230; 175; 72; 160; 59; 191; 210; 94; 140; 208; 54; 65; 65; 160; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 254; 186; 174; 220; 230; 175; 72; 160; 59; 191; 210; 94; 140; 208; 54; 65; 65].

  Lemma native_fixture_invalid_r_and_s_is_rejected :
    TransactionAuth.authenticate 1 None invalid_r_and_s_raw =
    TransactionAuth.Result.Rejected TransactionAuth.Error.InvalidSignature.
  Proof. vm_compute. reflexivity. Qed.

  (* TransactionTests/ttSignature/ZeroSigTransaction.json; SHA256 fc22452be810fcdd599f85432683d8fe52d9b81e822f5721ef0433cbdd4db3b4. *)
  Definition invalid_v_0_raw : list Z := [223; 3; 1; 130; 199; 56; 148; 185; 79; 83; 116; 252; 229; 237; 188; 142; 42; 134; 151; 193; 83; 49; 103; 126; 110; 191; 11; 10; 128; 128; 128; 128].

  Lemma native_fixture_invalid_v_0_is_rejected :
    TransactionAuth.authenticate 1 None invalid_v_0_raw =
    TransactionAuth.Result.Rejected TransactionAuth.Error.InvalidSignature.
  Proof. vm_compute. reflexivity. Qed.

  (* TransactionTests/ttSignature/ZeroSigTransaction2.json; SHA256 9754311c71763b4dd8613a8334bc5ed52e5812f0e70d585e9a810f4f3057e3b7. *)
  Definition invalid_v_1_raw : list Z := [223; 3; 1; 130; 199; 56; 148; 185; 79; 83; 116; 252; 229; 237; 188; 142; 42; 134; 151; 193; 83; 49; 103; 126; 110; 191; 11; 10; 128; 1; 128; 128].

  Lemma native_fixture_invalid_v_1_is_rejected :
    TransactionAuth.authenticate 1 None invalid_v_1_raw =
    TransactionAuth.Result.Rejected TransactionAuth.Error.InvalidSignature.
  Proof. vm_compute. reflexivity. Qed.

  (* TransactionTests/ttSignature/WrongVRSTestIncorrectSize.json; SHA256 63196b6980c22c664ba171646fb9fef86181ff3f2f2ef766e45ffd6be2011263. *)
  Definition oversized_r_and_s_raw : list Z := [248; 99; 128; 1; 130; 82; 8; 148; 185; 79; 83; 116; 252; 229; 237; 188; 142; 42; 134; 151; 193; 83; 49; 103; 126; 110; 191; 11; 10; 128; 28; 162; 152; 255; 146; 18; 1; 85; 71; 38; 54; 125; 43; 232; 200; 4; 167; 255; 137; 204; 242; 133; 235; 197; 125; 255; 138; 228; 196; 75; 156; 25; 172; 74; 2; 195; 162; 136; 135; 50; 27; 229; 117; 200; 9; 95; 120; 157; 212; 199; 67; 223; 228; 44; 24; 32; 249; 35; 31; 152; 169; 98; 178; 16; 227; 172; 36; 82; 163; 2; 195].

  Lemma native_fixture_oversized_r_and_s_is_rejected :
    TransactionAuth.authenticate 1 None oversized_r_and_s_raw =
    TransactionAuth.Result.Rejected TransactionAuth.Error.InvalidSignature.
  Proof. vm_compute. reflexivity. Qed.

  (* TransactionTests/ttSignature/PointAtInfinity.json; SHA256 2bb7309eb0fe5f4e290d08af8226aeb5fdab278da1f69551d82f0e1c466d6b51. *)
  Definition point_at_infinity_raw : list Z := [248; 95; 1; 16; 130; 82; 8; 148; 240; 240; 240; 240; 240; 240; 240; 240; 240; 240; 240; 240; 240; 240; 240; 240; 240; 240; 240; 240; 1; 128; 28; 160; 111; 0; 16; 255; 76; 49; 194; 166; 208; 82; 108; 13; 65; 78; 108; 208; 26; 213; 210; 46; 21; 191; 255; 152; 175; 35; 134; 115; 102; 185; 77; 135; 160; 84; 19; 57; 45; 85; 97; 25; 19; 45; 167; 5; 111; 143; 181; 106; 145; 56; 163; 100; 70; 168; 164; 173; 113; 89; 201; 216; 146; 217; 243; 34; 132].

  Lemma native_fixture_point_at_infinity_is_rejected :
    TransactionAuth.authenticate 1 None point_at_infinity_raw =
    TransactionAuth.Result.Rejected TransactionAuth.Error.RecoveryFailed.
  Proof. vm_compute. reflexivity. Qed.

  (* TransactionTests/ttSignature/WrongVRSTestVOverflow.json; SHA256 3965d571c653721be8052c5a107f73bec72b3a249085d7bdc142c79b547f213e. *)
  Definition invalid_v_overflow_raw : list Z := [248; 97; 128; 1; 130; 82; 8; 148; 185; 79; 83; 116; 252; 229; 237; 188; 142; 42; 134; 151; 193; 83; 49; 103; 126; 110; 191; 11; 10; 128; 130; 1; 54; 160; 152; 255; 146; 18; 1; 85; 71; 38; 54; 125; 43; 232; 200; 4; 167; 255; 137; 204; 242; 133; 235; 197; 125; 255; 138; 228; 196; 75; 156; 25; 172; 74; 160; 136; 135; 50; 27; 229; 117; 200; 9; 95; 120; 157; 212; 199; 67; 223; 228; 44; 24; 32; 249; 35; 31; 152; 169; 98; 178; 16; 227; 172; 36; 82; 163].

  Lemma native_fixture_invalid_v_overflow_is_rejected :
    TransactionAuth.authenticate 1 None invalid_v_overflow_raw =
    TransactionAuth.Result.Rejected (TransactionAuth.Error.ChainIdMismatch 137 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma missing_declared_sender_is_recovered :
    sender (TransactionAuth.authenticate 1 None add11_raw) = Some 966588469268559010541288244128342317224451555083.
  Proof. vm_compute. reflexivity. Qed.

  Lemma incorrect_declared_sender_is_rejected :
    TransactionAuth.authenticate 1 (Some 0) add11_raw =
    TransactionAuth.Result.Rejected (TransactionAuth.Error.SenderMismatch 966588469268559010541288244128342317224451555083 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma unprotected_legacy_signature_does_not_require_chain_id :
    sender (TransactionAuth.authenticate 2 None add11_raw) = Some 966588469268559010541288244128342317224451555083.
  Proof. vm_compute. reflexivity. Qed.

  Lemma changing_legacy_v_to_zero_or_one_is_invalid :
    List.map (fun v => TransactionAuth.authenticate 1 None
      (rewrite_field 0 add11_raw 6 (uint_item v))) [0; 1] =
    List.repeat (TransactionAuth.Result.Rejected TransactionAuth.Error.InvalidSignature) 2.
  Proof. vm_compute. reflexivity. Qed.

  Lemma high_s_is_rejected_by_transaction_authentication :
    TransactionAuth.authenticate 1 None
      (rewrite_field 0 (rewrite_field 0 add11_raw 6 (uint_item 28)) 8
        (uint_item (Secp256k1.scalar_modulus - 44143290970459462921032592289320808731927705910002740664918494751259156246038))) =
    TransactionAuth.Result.Rejected TransactionAuth.Error.InvalidSignature.
  Proof. vm_compute. reflexivity. Qed.

  Lemma typed_parity_is_not_truncated_to_one_byte :
    List.map (fun v => TransactionAuth.authenticate 1 None
      (rewrite_field 1 access_list_raw 8 (uint_item v))) [2; 27; 256] =
    List.repeat (TransactionAuth.Result.Rejected TransactionAuth.Error.InvalidSignature) 3.
  Proof. vm_compute. reflexivity. Qed.

  Lemma typed_chain_id_is_checked_before_signature :
    TransactionAuth.authenticate 2 None (rewrite_field 1 access_list_raw 8 (uint_item 2)) =
    TransactionAuth.Result.Rejected (TransactionAuth.Error.ChainIdMismatch 1 2).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_creation_is_a_canonical_envelope_error :
    TransactionAuth.authenticate 1 None
      (rewrite_field 3 blob_raw 5 (EthereumRlp.Item.Bytes [])) =
    TransactionAuth.Result.Rejected TransactionAuth.Error.MalformedFields.
  Proof. vm_compute. reflexivity. Qed.

  Lemma zero_integer_byte_is_noncanonical :
    TransactionAuth.authenticate 1 None
      (rewrite_field 0 add11_raw 0 (EthereumRlp.Item.Bytes [0])) =
    TransactionAuth.Result.Rejected TransactionAuth.Error.MalformedFields.
  Proof. vm_compute. reflexivity. Qed.

  Lemma malformed_type4_is_rejected :
    TransactionAuth.authenticate 1 None [4; 192] =
    TransactionAuth.Result.Rejected TransactionAuth.Error.MalformedFields.
  Proof. vm_compute. reflexivity. Qed.

  Lemma network_blob_sidecar_requires_separate_verification :
    TransactionAuth.authenticate 1 None [3; 196; 192; 192; 192; 192] =
    TransactionAuth.Result.Unsupported TransactionAuth.Unsupported.BlobSidecar.
  Proof. vm_compute. reflexivity. Qed.
  (* TransactionTests/ttVValue/V_equals37.json; SHA256 d0a327b7ee0eeddcd68e3286f33b29c21d20fafb0af533cb93c134e20f8a634d. *)
  Definition v_equals37_raw : list Z := [248; 101; 128; 134; 152; 133; 40; 64; 164; 111; 130; 214; 216; 148; 9; 94; 123; 174; 166; 166; 199; 196; 194; 223; 235; 151; 126; 250; 195; 38; 175; 85; 45; 135; 128; 128; 37; 160; 152; 255; 146; 18; 1; 85; 71; 38; 54; 125; 43; 232; 200; 4; 167; 255; 137; 204; 242; 133; 235; 197; 125; 255; 138; 228; 196; 75; 156; 25; 172; 74; 160; 24; 135; 50; 27; 229; 117; 200; 9; 95; 120; 157; 212; 199; 67; 223; 228; 44; 24; 32; 249; 35; 31; 152; 169; 98; 178; 16; 227; 172; 36; 82; 163].

  Lemma protected_legacy_v_equals37_recovers_native_sender :
    sender (TransactionAuth.authenticate 1 None v_equals37_raw) = Some 266395076419694023037738537452765201663280922664.
  Proof. vm_compute. reflexivity. Qed.

  Lemma protected_legacy_v_equals37_signing_hash_matches_reference :
    decoded_hash v_equals37_raw = Some 26940172353607395124742258045217990754387782013473789865718216536210868532918.
  Proof. vm_compute. reflexivity. Qed.

  (* TransactionTests/ttVValue/V_equals38.json; SHA256 150ba26fe5f2f67a937420f4848cee38d34334d4655242e9758cc46b98463fe9. *)
  Definition v_equals38_raw : list Z := [248; 126; 128; 159; 3; 30; 234; 64; 143; 142; 23; 153; 203; 136; 61; 162; 146; 123; 19; 54; 82; 29; 115; 194; 193; 74; 204; 254; 187; 112; 213; 197; 174; 70; 105; 130; 82; 8; 148; 9; 94; 123; 174; 166; 166; 199; 196; 194; 223; 235; 151; 126; 250; 195; 38; 175; 85; 45; 135; 128; 128; 38; 160; 152; 255; 146; 18; 1; 85; 71; 38; 54; 125; 43; 232; 200; 4; 167; 255; 137; 204; 242; 133; 235; 197; 125; 255; 138; 228; 196; 75; 156; 25; 172; 74; 160; 24; 135; 50; 27; 229; 117; 200; 9; 95; 120; 157; 212; 199; 67; 223; 228; 44; 24; 32; 249; 35; 31; 152; 169; 98; 178; 16; 227; 172; 36; 82; 163].

  Lemma protected_legacy_v_equals38_recovers_native_sender :
    sender (TransactionAuth.authenticate 1 None v_equals38_raw) = Some 900078559331821800077022732710384633134377881606.
  Proof. vm_compute. reflexivity. Qed.

  Lemma protected_legacy_v_equals38_signing_hash_matches_reference :
    decoded_hash v_equals38_raw = Some 23168896401301295607780620401482155790589977816436500104763679798784572412248.
  Proof. vm_compute. reflexivity. Qed.

  Lemma protected_legacy_chain_id_is_enforced :
    TransactionAuth.authenticate 2 None v_equals37_raw =
    TransactionAuth.Result.Rejected (TransactionAuth.Error.ChainIdMismatch 1 2).
  Proof. vm_compute. reflexivity. Qed.

  Lemma small_invalid_v_preserves_native_uint64_chain_id_derivation :
    TransactionAuth.legacy_chain_id 2 = Some 9223372036854775791.
  Proof. vm_compute. reflexivity. Qed.

  Lemma historical_too_few_rlp_fields_are_rejected :
    TransactionAuth.authenticate 1 None [248; 94; 128; 1; 130; 82; 8; 148; 9; 94; 123; 174; 166; 166; 199; 196; 194; 223; 235; 151; 126; 250; 195; 38; 175; 85; 45; 135; 10; 27; 160; 72; 181; 91; 250; 145; 90; 199; 149; 196; 49; 151; 141; 138; 106; 153; 43; 98; 141; 85; 125; 165; 255; 117; 155; 48; 125; 73; 90; 54; 100; 147; 83; 160; 239; 255; 211; 16; 172; 116; 63; 55; 29; 227; 185; 247; 249; 203; 86; 192; 178; 138; 212; 54; 1; 180; 171; 148; 159; 83; 250; 160; 123; 210; 200; 4] =
    TransactionAuth.Result.Rejected TransactionAuth.Error.MalformedFields.
  Proof. vm_compute. reflexivity. Qed.

  Lemma historical_too_many_rlp_fields_are_rejected :
    TransactionAuth.authenticate 1 None [248; 96; 128; 1; 130; 82; 8; 148; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 11; 147; 49; 103; 126; 110; 191; 10; 128; 28; 160; 152; 255; 146; 18; 1; 85; 71; 38; 54; 125; 43; 232; 200; 4; 167; 255; 137; 204; 242; 133; 235; 197; 125; 255; 138; 228; 196; 75; 156; 25; 172; 74; 160; 24; 135; 50; 27; 229; 117; 200; 9; 95; 120; 157; 212; 199; 67; 223; 228; 44; 24; 32; 249; 35; 31; 152; 169; 98; 178; 16; 227; 172; 36; 82; 163; 128] =
    TransactionAuth.Result.Rejected TransactionAuth.Error.MalformedFields.
  Proof. vm_compute. reflexivity. Qed.


  (** High-s counterpart of the historical add11 signature. Reversing parity
      together with s -> N-s preserves the recovered signer and transaction. *)
  Definition high_s_add11_raw :=
    rewrite_field 0 (rewrite_field 0 add11_raw 6 (uint_item 28)) 8
      (uint_item (Secp256k1.scalar_modulus -
        44143290970459462921032592289320808731927705910002740664918494751259156246038)).

  Lemma frontier_high_s_signature_recovers_historical_sender :
    sender (TransactionAuth.authenticate_for_spec SpecId.FRONTIER 1 None high_s_add11_raw) =
    Some 966588469268559010541288244128342317224451555083.
  Proof. vm_compute. reflexivity. Qed.

  Lemma frontier_thawing_high_s_signature_recovers_historical_sender :
    sender (TransactionAuth.authenticate_for_spec SpecId.FRONTIER_THAWING 1 None high_s_add11_raw) =
    Some 966588469268559010541288244128342317224451555083.
  Proof. vm_compute. reflexivity. Qed.

  Lemma homestead_high_s_signature_is_rejected :
    TransactionAuth.authenticate_for_spec SpecId.HOMESTEAD 1 None high_s_add11_raw =
    TransactionAuth.Result.Rejected TransactionAuth.Error.InvalidSignature.
  Proof. vm_compute. reflexivity. Qed.

  Lemma protected_legacy_before_spurious_is_invalid_signature :
    List.map (fun spec => TransactionAuth.authenticate_for_spec spec 1 None v_equals37_raw)
      [SpecId.FRONTIER; SpecId.HOMESTEAD; SpecId.TANGERINE] =
    List.repeat (TransactionAuth.Result.Rejected TransactionAuth.Error.InvalidSignature) 3.
  Proof. vm_compute. reflexivity. Qed.

  Lemma protected_legacy_before_spurious_does_not_compare_chain_id :
    TransactionAuth.authenticate_for_spec SpecId.TANGERINE 2 None v_equals37_raw =
    TransactionAuth.Result.Rejected TransactionAuth.Error.InvalidSignature.
  Proof. vm_compute. reflexivity. Qed.

  Lemma protected_legacy_at_spurious_recovers_historical_sender :
    sender (TransactionAuth.authenticate_for_spec SpecId.SPURIOUS_DRAGON 1 None v_equals37_raw) =
    Some 266395076419694023037738537452765201663280922664.
  Proof. vm_compute. reflexivity. Qed.

  Lemma protected_legacy_at_spurious_checks_chain_id :
    TransactionAuth.authenticate_for_spec SpecId.SPURIOUS_DRAGON 2 None v_equals37_raw =
    TransactionAuth.Result.Rejected (TransactionAuth.Error.ChainIdMismatch 1 2).
  Proof. vm_compute. reflexivity. Qed.

  Lemma unprotected_legacy_at_frontier_ignores_chain_id :
    sender (TransactionAuth.authenticate_for_spec SpecId.FRONTIER 2 None add11_raw) =
    Some 966588469268559010541288244128342317224451555083.
  Proof. vm_compute. reflexivity. Qed.

  Lemma access_list_before_berlin_is_rejected :
    TransactionAuth.authenticate_for_spec SpecId.ISTANBUL 1 None access_list_raw =
    TransactionAuth.Result.Rejected (TransactionAuth.Error.TransactionTypeNotSupported 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma access_list_at_berlin_recovers_historical_sender :
    sender (TransactionAuth.authenticate_for_spec SpecId.BERLIN 1 None access_list_raw) =
    Some 966588469268559010541288244128342317224451555083.
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_fee_before_london_is_rejected :
    TransactionAuth.authenticate_for_spec SpecId.BERLIN 1 None dynamic_fee_raw =
    TransactionAuth.Result.Rejected (TransactionAuth.Error.TransactionTypeNotSupported 2).
  Proof. vm_compute. reflexivity. Qed.

  Lemma dynamic_fee_at_london_recovers_historical_sender :
    sender (TransactionAuth.authenticate_for_spec SpecId.LONDON 1 None dynamic_fee_raw) =
    Some 966588469268559010541288244128342317224451555083.
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_before_cancun_is_rejected :
    TransactionAuth.authenticate_for_spec SpecId.SHANGHAI 1 None blob_raw =
    TransactionAuth.Result.Rejected (TransactionAuth.Error.TransactionTypeNotSupported 3).
  Proof. vm_compute. reflexivity. Qed.

  Lemma blob_at_cancun_recovers_historical_sender :
    sender (TransactionAuth.authenticate_for_spec SpecId.CANCUN 1 None blob_raw) =
    Some 966588469268559010541288244128342317224451555083.
  Proof. vm_compute. reflexivity. Qed.

  Lemma typed_activation_is_checked_before_chain_id_and_signature :
    TransactionAuth.authenticate_for_spec SpecId.ISTANBUL 2 None
      (rewrite_field 1 access_list_raw 8 (uint_item 2)) =
    TransactionAuth.Result.Rejected (TransactionAuth.Error.TransactionTypeNotSupported 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma active_typed_chain_id_is_checked_before_signature :
    TransactionAuth.authenticate_for_spec SpecId.BERLIN 2 None
      (rewrite_field 1 access_list_raw 8 (uint_item 2)) =
    TransactionAuth.Result.Rejected (TransactionAuth.Error.ChainIdMismatch 1 2).
  Proof. vm_compute. reflexivity. Qed.

  Lemma decoding_precedes_typed_activation :
    TransactionAuth.authenticate_for_spec SpecId.FRONTIER 1 None [1; 192] =
    TransactionAuth.Result.Rejected TransactionAuth.Error.MalformedFields.
  Proof. vm_compute. reflexivity. Qed.

  Lemma homestead_high_s_still_rejects_with_wrong_declared_sender :
    TransactionAuth.authenticate_for_spec SpecId.HOMESTEAD 1 (Some 0) high_s_add11_raw =
    TransactionAuth.Result.Rejected TransactionAuth.Error.InvalidSignature.
  Proof. vm_compute. reflexivity. Qed.

  Definition authorization_fields (nonce parity : Z) : EthereumRlp.Item.t :=
    EthereumRlp.Item.List [
      EthereumRlp.Item.Bytes [1]; EthereumRlp.Item.Bytes (List.repeat 0 20);
      EthereumRlp.Item.Bytes (EthereumRlp.big_endian nonce);
      EthereumRlp.Item.Bytes (EthereumRlp.big_endian parity);
      EthereumRlp.Item.Bytes [1]; EthereumRlp.Item.Bytes [1]].

  Definition set_code_fields : list EthereumRlp.Item.t := [
    EthereumRlp.Item.Bytes [1]; EthereumRlp.Item.Bytes [];
    EthereumRlp.Item.Bytes [1]; EthereumRlp.Item.Bytes [2];
    EthereumRlp.Item.Bytes [1; 134; 160]; EthereumRlp.Item.Bytes (List.repeat 0 20);
    EthereumRlp.Item.Bytes []; EthereumRlp.Item.Bytes []; EthereumRlp.Item.List [];
    EthereumRlp.Item.List [authorization_fields 0 1];
    EthereumRlp.Item.Bytes []; EthereumRlp.Item.Bytes [1]; EthereumRlp.Item.Bytes [1]].

  Lemma set_code_decodes_and_preserves_signing_payload :
    match TransactionAuth.decode_fields 4 set_code_fields with
    | Some envelope =>
        List.length envelope.(TransactionAuth.Envelope.transaction).(TransactionAccounting.Transaction.authorization_list) = 1%nat /\
        envelope.(TransactionAuth.Envelope.signing_payload) =
          4 :: EthereumRlp.encode (EthereumRlp.Item.List (List.firstn 10 set_code_fields))
    | None => False
    end.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma authorization_nonce_overflow_rejected :
    TransactionAuth.authorization (authorization_fields (2 ^ 64) 0) = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma authorization_parity_overflow_rejected :
    TransactionAuth.authorization (authorization_fields 0 256) = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma set_code_not_enabled_before_prague :
    TransactionAuth.authenticate_for_spec SpecId.CANCUN 1 None
      (4 :: EthereumRlp.encode (EthereumRlp.Item.List set_code_fields)) =
      TransactionAuth.Result.Rejected (TransactionAuth.Error.TransactionTypeNotSupported 4).
  Proof. vm_compute. reflexivity. Qed.

End Test.
