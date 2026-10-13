From Stdlib Require Import ZArith.

Require Import revm.revm_precompile.simulate.bn254_pairing.
Require Import revm.revm_precompile.simulate.bn254_tower.

Open Scope Z_scope.

Module Test.
  Module Fq2 := Bn254Pairing.Fq2.

  Module Fq6 := Bn254Tower.Fq6.

  Module Fq12 := Bn254Tower.Fq12.

  Definition a : Fq6.t := Fq6.make
    (Fq2.make 1 2) (Fq2.make 3 4) (Fq2.make 5 6).

  Definition b : Fq6.t := Fq6.make
    (Fq2.make 7 8) (Fq2.make 9 10) (Fq2.make 11 12).

  Definition x : Fq12.t := Fq12.make a b.

  Lemma cubic_relation :
    Fq6.mul (Fq6.mul Fq6.v Fq6.v) Fq6.v =
      Fq6.make Fq2.xi Fq2.zero Fq2.zero.
  Proof. vm_compute. reflexivity. Qed.

  Lemma independent_fq6_product :
    Fq6.mul a b = Fq6.make
      (Fq2.make (-463) 1648)
      (Fq2.make (-301) 1197)
      (Fq2.make (-39) 182).
  Proof. vm_compute. reflexivity. Qed.

  Lemma fq6_inverse : Fq6.mul a (Fq6.inverse a) = Fq6.one.
  Proof. vm_compute. reflexivity. Qed.

  Lemma quadratic_relation :
    Fq12.mul Fq12.w Fq12.w = Fq12.make Fq6.v Fq6.zero.
  Proof. vm_compute. reflexivity. Qed.

  Lemma fq12_inverse : Fq12.mul x (Fq12.inverse x) = Fq12.one.
  Proof. vm_compute. reflexivity. Qed.

  Lemma fq12_power_three :
    Fq12.pow x 3 = Fq12.mul (Fq12.square x) x.
  Proof. vm_compute. reflexivity. Qed.
End Test.
