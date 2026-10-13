From Stdlib Require Import ZArith.

Require Import revm.revm_precompile.simulate.bn254_pairing.
Require Import revm.revm_precompile.simulate.bn254_tower.

Open Scope Z_scope.

(** Frobenius maps for the BN254 tower. All constants are normal residues of
    powers of xi=9+i; the coefficient order here is real, imaginary. *)
Module Bn254Frobenius.
  Module Fq2 := Bn254Pairing.Fq2.

  Module Fq6 := Bn254Tower.Fq6.

  Module Fq12 := Bn254Tower.Fq12.

  Definition xi_p_minus_1_over_6 : Fq2.t := Fq2.make
    8376118865763821496583973867626364092589906065868298776909617916018768340080
    16469823323077808223889137241176536799009286646108169935659301613961712198316.

  Definition xi_p_minus_1_over_3 : Fq2.t := Fq2.make
    21575463638280843010398324269430826099269044274347216827212613867836435027261
    10307601595873709700152284273816112264069230130616436755625194854815875713954.

  Definition xi_p_minus_1_over_2 : Fq2.t := Fq2.make
    2821565182194536844548159561693502659359617185244120367078079554186484126554
    3505843767911556378687030309984248845540243509899259641013678093033130930403.

  Definition xi_2p_minus_2_over_3 : Fq2.t := Fq2.make
    2581911344467009335267311115468803099551665605076196740867805258568234346338
    19937756971775647987995932169929341994314640652964949448313374472400716661030.

  Definition xi_p2_minus_1_over_3 : Z :=
    21888242871839275220042445260109153167277707414472061641714758635765020556616.

  Definition xi_2p2_minus_2_over_3 : Z :=
    2203960485148121921418603742825762020974279258880205651966.

  Definition xi_p2_minus_1_over_6 : Z :=
    21888242871839275220042445260109153167277707414472061641714758635765020556617.

  Definition fq2_p (value : Fq2.t) : Fq2.t :=
    Fq2.make value.(Fq2.real) (- value.(Fq2.imag)).

  Definition fq6_p (value : Fq6.t) : Fq6.t :=
    Fq6.make
      (fq2_p value.(Fq6.c0))
      (Fq2.mul (fq2_p value.(Fq6.c1)) xi_p_minus_1_over_3)
      (Fq2.mul (fq2_p value.(Fq6.c2)) xi_2p_minus_2_over_3).

  Definition fq6_p2 (value : Fq6.t) : Fq6.t :=
    Fq6.make value.(Fq6.c0)
      (Fq2.mul_z value.(Fq6.c1) xi_p2_minus_1_over_3)
      (Fq2.mul_z value.(Fq6.c2) xi_2p2_minus_2_over_3).

  Definition fq12_p (value : Fq12.t) : Fq12.t :=
    Fq12.make (fq6_p value.(Fq12.c0))
      (Fq6.mul_fq2 (fq6_p value.(Fq12.c1)) xi_p_minus_1_over_6).

  Definition fq12_p2 (value : Fq12.t) : Fq12.t :=
    Fq12.make (fq6_p2 value.(Fq12.c0))
      (Fq6.mul_fq2 (fq6_p2 value.(Fq12.c1))
        (Fq2.of_z xi_p2_minus_1_over_6)).
End Bn254Frobenius.
