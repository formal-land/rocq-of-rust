From Stdlib Require Import List ZArith.

Require Import revm.revm_precompile.simulate.bn254_pairing_run.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition geth_one_point : list Z :=
    [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 25; 142; 147; 147; 146; 13; 72; 58; 114; 96; 191; 183; 49; 251; 93; 37; 241; 170; 73; 51; 53; 169; 231; 18; 151; 228; 133; 183; 174; 243; 18; 194; 24; 0; 222; 239; 18; 31; 30; 118; 66; 106; 0; 102; 94; 92; 68; 121; 103; 67; 34; 212; 247; 94; 218; 221; 70; 222; 189; 92; 217; 146; 246; 237; 9; 6; 137; 208; 88; 95; 240; 117; 236; 158; 153; 173; 105; 12; 51; 149; 188; 75; 49; 51; 112; 179; 142; 243; 85; 172; 218; 220; 209; 34; 151; 91; 18; 200; 94; 165; 219; 140; 109; 235; 74; 171; 113; 128; 141; 203; 64; 143; 227; 209; 231; 105; 12; 67; 211; 123; 76; 230; 204; 1; 102; 250; 125; 170].

  Lemma empty_input_istanbul :
    Bn254PairingRun.run 45000 34000 [] 45000 =
      Bn254PairingRun.Result.Success 45000 (List.repeat 0 31 ++ [1]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_input_byzantium :
    Bn254PairingRun.run 100000 80000 [] 100000 =
      Bn254PairingRun.Result.Success 100000 (List.repeat 0 31 ++ [1]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_oog_boundary :
    Bn254PairingRun.run 45000 34000 [] 44999 =
      Bn254PairingRun.Result.OutOfGas.
  Proof. vm_compute. reflexivity. Qed.

  Lemma malformed_191 :
    Bn254PairingRun.run 45000 34000 (List.repeat 0 191) 45000 =
      Bn254PairingRun.Result.InvalidLength.
  Proof. vm_compute. reflexivity. Qed.

  Lemma malformed_193_oog_first :
    Bn254PairingRun.run 45000 34000 (List.repeat 0 193) 78999 =
      Bn254PairingRun.Result.OutOfGas.
  Proof. vm_compute. reflexivity. Qed.

  Lemma malformed_193_at_cost :
    Bn254PairingRun.run 45000 34000 (List.repeat 0 193) 79000 =
      Bn254PairingRun.Result.InvalidLength.
  Proof. vm_compute. reflexivity. Qed.

  Lemma infinity_pair :
    Bn254PairingRun.run 45000 34000 (List.repeat 0 192) 79000 =
      Bn254PairingRun.Result.Success 79000 (List.repeat 0 31 ++ [1]).
  Proof. vm_compute. reflexivity. Qed.

  (** Geth core/vm/testdata/precompiles/bn256Pairing.json: one_point. *)
  Lemma official_one_point_false :
    Bn254PairingRun.run 45000 34000 geth_one_point 79000 =
      Bn254PairingRun.Result.Success 79000 (List.repeat 0 32).
  Proof. vm_compute. reflexivity. Qed.
End Test.
