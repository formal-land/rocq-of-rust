From Stdlib Require Import ZArith.

Require Import revm.revm_precompile.simulate.bn254_tower.
Require Import revm.revm_precompile.simulate.bn254_frobenius.

Open Scope Z_scope.

(** Final exponentiation of a nonzero BN254 Miller product. The Frobenius
    chain follows the local go-ethereum/crypto/bn256/google/optate.go. *)
Module Bn254FinalExp.
  Module Fq12 := Bn254Tower.Fq12.
  Definition u : Z := 4965661367192848881.

  Definition run (value : Fq12.t) : Fq12.t :=
    let easy := Fq12.mul (Fq12.conjugate value) (Fq12.inverse value) in
    let easy := Fq12.mul easy (Bn254Frobenius.fq12_p2 easy) in
    let fp := Bn254Frobenius.fq12_p easy in
    let fp2 := Bn254Frobenius.fq12_p2 easy in
    let fp3 := Bn254Frobenius.fq12_p fp2 in
    let fu := Fq12.pow easy u in
    let fu2 := Fq12.pow fu u in
    let fu3 := Fq12.pow fu2 u in
    let y3 := Fq12.conjugate (Bn254Frobenius.fq12_p fu) in
    let fu2p := Bn254Frobenius.fq12_p fu2 in
    let fu3p := Bn254Frobenius.fq12_p fu3 in
    let y2 := Bn254Frobenius.fq12_p2 fu2 in
    let y0 := Fq12.mul (Fq12.mul fp fp2) fp3 in
    let y1 := Fq12.conjugate easy in
    let y5 := Fq12.conjugate fu2 in
    let y4 := Fq12.conjugate (Fq12.mul fu fu2p) in
    let y6 := Fq12.conjugate (Fq12.mul fu3 fu3p) in
    let t0 := Fq12.mul (Fq12.mul (Fq12.square y6) y4) y5 in
    let t1 := Fq12.mul (Fq12.mul y3 y5) t0 in
    let t0 := Fq12.mul t0 y2 in
    let t1 := Fq12.mul (Fq12.square t1) t0 in
    let t1 := Fq12.square t1 in
    let t0 := Fq12.mul t1 y1 in
    let t1 := Fq12.mul t1 y0 in
    Fq12.mul (Fq12.square t0) t1.
End Bn254FinalExp.
