From Stdlib Require Import List ZArith.
Require Import revm.revm_handler.simulate.ethereum_rlp.
Require Import revm.revm_handler.simulate.transaction_validation.
Require Import revm.revm_primitives.links.hardfork.
Import ListNotations.
Open Scope Z_scope.

Module Test.
  (** tests/frontier/validation/test_transaction.py::test_tx_nonce_overflow[fork_Berlin-transaction_test]; fixtures/transaction_tests/for_berlin/frontier/validation/transaction/tx_nonce_overflow.json. *)
  Definition nonce_overflow_raw : list Z :=
    [248; 104; 137; 1; 0; 0; 0; 0; 0; 0; 0; 0; 10; 130; 82; 8; 148; 192; 246; 220; 158; 88; 54; 245; 76; 170; 219; 245; 156; 198; 147; 70; 197; 8; 225; 153; 43; 128; 128; 28; 160; 55; 246; 139; 158; 166; 122; 169; 109; 206; 248; 6; 230; 145; 49; 75; 236; 73; 208; 214; 167; 176; 218; 67; 52; 127; 216; 144; 122; 70; 105; 68; 237; 160; 89; 185; 86; 120; 22; 37; 115; 252; 68; 12; 37; 177; 193; 19; 57; 183; 112; 1; 83; 205; 194; 254; 2; 151; 96; 199; 229; 88; 17; 34; 40; 46].
  Lemma nonce_overflow :
    TransactionValidation.validate SpecId.FRONTIER 1 nonce_overflow_raw =
    TransactionValidation.Result.Rejected TransactionValidation.Rejection.MalformedEnvelope.
  Proof. vm_compute. reflexivity. Qed.

  (** tests/prague/eip7702_set_code_tx/test_invalid_tx.py::test_invalid_tx_invalid_address[fork_Osaka-transaction_test-non_zero_address-oversized]; fixtures/transaction_tests/for_osaka/prague/eip7702_set_code_tx/invalid_tx/invalid_tx_invalid_address.json. *)
  Definition invalid_auth_format_raw : list Z :=
    [4; 248; 194; 1; 128; 128; 7; 131; 1; 134; 160; 148; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 128; 128; 192; 248; 93; 248; 91; 128; 149; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 128; 128; 160; 86; 153; 58; 43; 220; 56; 145; 22; 133; 78; 114; 215; 87; 81; 189; 101; 144; 92; 31; 108; 74; 72; 66; 125; 140; 225; 39; 149; 162; 228; 173; 147; 160; 73; 98; 28; 25; 13; 112; 188; 5; 188; 35; 211; 26; 156; 100; 254; 24; 142; 227; 78; 57; 253; 213; 132; 101; 8; 175; 106; 182; 80; 15; 185; 130; 1; 160; 103; 217; 206; 184; 20; 73; 51; 94; 141; 48; 45; 11; 77; 71; 115; 157; 246; 145; 24; 109; 98; 212; 181; 20; 166; 252; 57; 176; 166; 200; 154; 201; 160; 30; 1; 42; 131; 197; 173; 219; 184; 42; 13; 22; 98; 165; 217; 187; 11; 51; 149; 62; 221; 29; 207; 135; 129; 68; 54; 155; 93; 126; 25; 225; 150].
  Lemma invalid_auth_format :
    TransactionValidation.validate SpecId.PRAGUE 1 invalid_auth_format_raw =
    TransactionValidation.Result.Rejected TransactionValidation.Rejection.MalformedEnvelope.
  Proof. vm_compute. reflexivity. Qed.

  (** tests/prague/eip7702_set_code_tx/test_invalid_tx.py::test_invalid_auth_signature[fork_Osaka-transaction_test-non_zero_address-r=2**256]; fixtures/transaction_tests/for_osaka/prague/eip7702_set_code_tx/invalid_tx/invalid_auth_signature.json. *)
  Definition invalid_auth_signature_width_raw : list Z :=
    [4; 248; 162; 1; 128; 128; 7; 131; 1; 134; 160; 148; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 128; 128; 192; 248; 61; 248; 59; 1; 148; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 128; 1; 161; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 160; 191; 190; 125; 161; 208; 32; 16; 30; 43; 122; 105; 233; 139; 141; 155; 134; 177; 199; 66; 117; 251; 51; 8; 10; 127; 158; 134; 209; 67; 43; 96; 38; 160; 9; 8; 77; 102; 60; 117; 254; 207; 196; 219; 250; 84; 100; 245; 32; 223; 36; 233; 76; 150; 59; 9; 138; 68; 31; 38; 48; 42; 171; 1; 105; 189].
  Lemma invalid_auth_signature_width :
    TransactionValidation.validate SpecId.OSAKA 1 invalid_auth_signature_width_raw =
    TransactionValidation.Result.Rejected TransactionValidation.Rejection.MalformedEnvelope.
  Proof. vm_compute. reflexivity. Qed.

  (** tests/prague/eip7702_set_code_tx/test_invalid_tx.py::test_empty_authorization_list[fork_Osaka-transaction_test]; fixtures/transaction_tests/for_osaka/prague/eip7702_set_code_tx/invalid_tx/empty_authorization_list.json. *)
  Definition empty_authorizations_raw : list Z :=
    [4; 248; 100; 1; 128; 128; 7; 131; 1; 134; 160; 148; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 128; 128; 192; 192; 1; 160; 136; 75; 244; 133; 25; 157; 94; 134; 230; 117; 231; 159; 23; 167; 16; 183; 84; 163; 105; 21; 163; 58; 40; 56; 194; 78; 30; 83; 55; 134; 153; 241; 160; 116; 8; 92; 161; 42; 208; 247; 41; 182; 189; 108; 55; 167; 162; 62; 146; 92; 126; 30; 135; 165; 87; 173; 49; 0; 169; 17; 55; 134; 201; 138; 253].
  Lemma empty_authorizations :
    TransactionValidation.validate SpecId.PRAGUE 1 empty_authorizations_raw =
    TransactionValidation.Result.Rejected TransactionValidation.Rejection.EmptyAuthorizationList.
  Proof. vm_compute. reflexivity. Qed.

End Test.
