(** Consensus vectors from pinned tests@v20.0.2 Berlin blockchain fixtures.
    Their transaction and receipt roots are fixture header fields. *)
From Stdlib Require Import List ZArith.

Require Import revm.revm_handler.simulate.ethereum_block_commitment.
Require Import revm.revm_handler.simulate.eest_types.

Import ListNotations.
Import EthereumBlockCommitment.
Open Scope Z_scope.

Module Test.
  Definition legacy_tx : list Z := [248; 82; 128; 10; 132; 7; 39; 14; 0; 128; 128; 133; 96; 0; 96; 0; 253; 28; 160; 75; 181; 145; 108; 211; 49; 71; 120; 72; 236; 169; 234; 214; 65; 158; 137; 34; 207; 207; 222; 82; 155; 118; 160; 25; 50; 155; 94; 142; 230; 46; 81; 160; 74; 75; 165; 121; 136; 34; 10; 70; 18; 247; 182; 125; 5; 14; 230; 87; 155; 32; 191; 178; 73; 94; 42; 104; 96; 62; 72; 113; 84; 89; 206; 121].

  Lemma legacy_transaction_root :
    transaction_root [legacy_tx] = Some [199; 175; 135; 42; 191; 214; 167; 32; 188; 52; 165; 75; 159; 69; 138; 51; 16; 34; 128; 62; 68; 207; 207; 239; 200; 172; 106; 41; 210; 70; 43; 242].
  Proof. vm_compute. reflexivity. Qed.

  Definition failed_legacy_receipt : Receipt.t := {|
    Receipt.transaction_type := 0;
    Receipt.outcome := Receipt.Outcome.Status false;
    Receipt.cumulative_gas_used := 120000000;
    Receipt.logs := [];
  |}.

  Lemma legacy_receipt_root :
    receipts_root [failed_legacy_receipt] = Some [107; 28; 43; 24; 150; 29; 49; 193; 25; 82; 57; 92; 94; 6; 203; 55; 105; 50; 218; 203; 26; 187; 36; 32; 66; 149; 242; 180; 167; 39; 56; 183].
  Proof. vm_compute. reflexivity. Qed.

  Definition successful_typed_receipt : Receipt.t := {|
    Receipt.transaction_type := 1;
    Receipt.outcome := Receipt.Outcome.Status true;
    Receipt.cumulative_gas_used := 62105;
    Receipt.logs := [];
  |}.

  Lemma typed_receipt_root :
    receipts_root [successful_typed_receipt] = Some [94; 251; 84; 54; 46; 221; 69; 113; 67; 227; 219; 71; 234; 211; 42; 185; 79; 143; 14; 208; 193; 99; 39; 213; 111; 77; 169; 191; 104; 167; 147; 189].
  Proof. vm_compute. reflexivity. Qed.

  Definition sample_log : EestTypes.EvmLog.t := {|
    EestTypes.EvmLog.address := 66051;
    EestTypes.EvmLog.topics := [263430; 11259375];
    EestTypes.EvmLog.data := [7; 8; 9];
  |}.

  Lemma log_bloom_reference : bloom_value [sample_log] = 778003621321024646393609123396689674168325413748251209692091200949627260375103977437569908027826864579780674936382995570364260182292975110699844305458663147042617421005679430683168077361894317465866853936734688517251386903666926362326565472091813775806376535094777817906071628945502658516070442913043626501570244123215218743998420789955556992486104555973139451893193009193290163669243725443947532922269216510163221387558959882652052495653434024904887695917646979074146313033842328061846944458843793616823277087376046029604496142297830922314816037769019849300922279584861424627744768.
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_block_bloom :
    block_bloom [] = Some (List.repeat 0 256).
  Proof. vm_compute. reflexivity. Qed.

  Lemma invalid_transaction_byte : transaction_root [[256]] = None.
  Proof. vm_compute. reflexivity. Qed.

  Lemma invalid_receipt_gas :
    receipts_root [{|
      Receipt.transaction_type := 0;
      Receipt.outcome := Receipt.Outcome.Status true;
      Receipt.cumulative_gas_used := 2 ^ 64;
      Receipt.logs := [] |}] = None.
  Proof. vm_compute. reflexivity. Qed.
End Test.
