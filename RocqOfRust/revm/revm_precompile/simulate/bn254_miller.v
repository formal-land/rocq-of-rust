From Stdlib Require Import Bool List ZArith.

Require Import revm.revm_precompile.simulate.bn254_pairing.
Require Import revm.revm_precompile.simulate.bn254_tower.

Import ListNotations.
Open Scope Z_scope.

(** Optimal Ate Miller loop for BN254. The formulas follow the local
    go-ethereum/crypto/bn256/google/optate.go in normal field residues;
    this is an executable arithmetic definition, not a correspondence proof. *)
Module Bn254Miller.
  Module Fq2 := Bn254Pairing.Fq2.

  Module G2 := Bn254Pairing.G2.

  Module Fq6 := Bn254Tower.Fq6.

  Module Fq12 := Bn254Tower.Fq12.

  Definition line (a b c : Fq2.t) : Fq12.t :=
    Fq12.make
      (Fq6.make c Fq2.zero Fq2.zero)
      (Fq6.make b a Fq2.zero).

  (** Return the new twist point and its line evaluated at affine G1 P. *)
  Definition line_double (r : G2.t) (p_x p_y : Z) : G2.t * Fq12.t :=
    let x := r.(G2.x) in
    let y := r.(G2.y) in
    let z := r.(G2.z) in
    let z2 := Fq2.square z in
    let a0 := Fq2.square x in
    let b0 := Fq2.square y in
    let c0 := Fq2.square b0 in
    let d := Fq2.mul_z
      (Fq2.sub (Fq2.sub (Fq2.square (Fq2.add x b0)) a0) c0) 2 in
    let e := Fq2.mul_z a0 3 in
    let g := Fq2.square e in
    let x3 := Fq2.sub g (Fq2.mul_z d 2) in
    let z3 := Fq2.sub (Fq2.sub (Fq2.square (Fq2.add y z)) b0) z2 in
    let y3 := Fq2.sub (Fq2.mul e (Fq2.sub d x3)) (Fq2.mul_z c0 8) in
    let line_a := Fq2.sub
      (Fq2.sub (Fq2.sub (Fq2.square (Fq2.add x e)) a0) g)
      (Fq2.mul_z b0 4) in
    let line_b := Fq2.negate (Fq2.mul_z (Fq2.mul e z2) (2 * p_x)) in
    let line_c := Fq2.mul_z (Fq2.mul z3 z2) (2 * p_y) in
    ({| G2.x := x3; G2.y := y3; G2.z := z3 |},
      line line_a line_b line_c).

  (** Mixed addition of Jacobian r and affine q, with the line at G1 P. *)
  Definition line_add (r q : G2.t) (p_x p_y : Z) : G2.t * Fq12.t :=
    let x := r.(G2.x) in
    let y := r.(G2.y) in
    let z := r.(G2.z) in
    let q_x := q.(G2.x) in
    let q_y := q.(G2.y) in
    let z2 := Fq2.square z in
    let q_y2 := Fq2.square q_y in
    let b0 := Fq2.mul q_x z2 in
    let d := Fq2.mul
      (Fq2.sub (Fq2.sub (Fq2.square (Fq2.add q_y z)) q_y2) z2) z2 in
    let h := Fq2.sub b0 x in
    let i := Fq2.square h in
    let e := Fq2.mul_z i 4 in
    let j := Fq2.mul h e in
    let l1 := Fq2.sub d (Fq2.mul_z y 2) in
    let v := Fq2.mul x e in
    let x3 := Fq2.sub (Fq2.sub (Fq2.square l1) j) (Fq2.mul_z v 2) in
    let z3 := Fq2.sub (Fq2.sub (Fq2.square (Fq2.add z h)) z2) i in
    let y3 := Fq2.sub (Fq2.mul (Fq2.sub v x3) l1)
      (Fq2.mul_z (Fq2.mul y j) 2) in
    let t := Fq2.sub
      (Fq2.sub (Fq2.square (Fq2.add q_y z3)) q_y2)
      (Fq2.square z3) in
    let line_a := Fq2.sub (Fq2.mul_z (Fq2.mul l1 q_x) 2) t in
    let line_b := Fq2.negate (Fq2.mul_z l1 (2 * p_x)) in
    let line_c := Fq2.mul_z z3 (2 * p_y) in
    ({| G2.x := x3; G2.y := y3; G2.z := z3 |},
      line line_a line_b line_c).

  (** Low bit first signed NAF of 6u+2, u=4965661367192848881. *)
  Definition six_u_plus_2_naf : list Z :=
    [0; 0; 0; 1; 0; 1; 0; -1; 0; 0; 1; -1; 0; 0; 1; 0;
     0; 1; 1; 0; -1; 0; 0; 1; 0; -1; 0; 0; 0; 0; 1; 1;
     1; 0; 0; -1; 0; 0; 1; 0; 0; 0; 0; 0; -1; 0; 0; 1;
     1; 0; 0; -1; 0; 0; 0; 1; 1; 0; -1; 0; 0; 1; 0; 1; 1].

  Definition loop_digits : list Z :=
    List.map (fun index => List.nth index six_u_plus_2_naf 0)
      (List.rev (List.seq 0 64)).

  Definition negate_affine_y (q : G2.t) : G2.t :=
    {| G2.x := q.(G2.x); G2.y := Fq2.negate q.(G2.y);
       G2.z := Fq2.one |}.

  Fixpoint loop (digits : list Z) (first : bool)
      (r q minus_q : G2.t) (p_x p_y : Z) (acc : Fq12.t) : G2.t * Fq12.t :=
    match digits with
    | [] => (r, acc)
    | digit :: rest =>
      let '(after_double, double_line) := line_double r p_x p_y in
      let acc := Fq12.mul
        (if first then acc else Fq12.square acc) double_line in
      let '(after_add, acc) :=
        if digit =? 1 then
          let '(next, add_line) := line_add after_double q p_x p_y in
          (next, Fq12.mul acc add_line)
        else if digit =? -1 then
          let '(next, add_line) := line_add after_double minus_q p_x p_y in
          (next, Fq12.mul acc add_line)
        else (after_double, acc) in
      loop rest false after_add q minus_q p_x p_y acc
    end.

  Definition fq2_conjugate (value : Fq2.t) : Fq2.t :=
    Fq2.make value.(Fq2.real) (- value.(Fq2.imag)).

  (** Frobenius-derived final two twist points. They are Q1 and -Q2 in
      optate.go, including the signs already encoded by their coordinates. *)
  Definition q1 (q : G2.t) : G2.t :=
    {| G2.x := Fq2.mul (fq2_conjugate q.(G2.x))
         (Fq2.make
           21575463638280843010398324269430826099269044274347216827212613867836435027261
           10307601595873709700152284273816112264069230130616436755625194854815875713954);
       G2.y := Fq2.mul (fq2_conjugate q.(G2.y))
         (Fq2.make
           2821565182194536844548159561693502659359617185244120367078079554186484126554
           3505843767911556378687030309984248845540243509899259641013678093033130930403);
       G2.z := Fq2.one |}.

  Definition minus_q2 (q : G2.t) : G2.t :=
    {| G2.x := Fq2.mul_z q.(G2.x)
         21888242871839275220042445260109153167277707414472061641714758635765020556616;
       G2.y := q.(G2.y);
       G2.z := Fq2.one |}.

  Definition run (p_x p_y : Z) (q : G2.t) : Fq12.t :=
    if ((p_x =? 0) && (p_y =? 0)) || G2.is_infinity q then Fq12.one else
    let '(r, acc) := loop loop_digits true q q (negate_affine_y q)
      p_x p_y Fq12.one in
    let '(r, first_line) := line_add r (q1 q) p_x p_y in
    let acc := Fq12.mul acc first_line in
    let '(_, second_line) := line_add r (minus_q2 q) p_x p_y in
    Fq12.mul acc second_line.
End Bn254Miller.
