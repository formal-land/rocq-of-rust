From Stdlib Require Import Bool ZArith.

Require Import revm.revm_precompile.simulate.bn254_pairing.

Open Scope Z_scope.

(** The extension-field tower used by the BN254 optimal Ate pairing:
    Fq2 = Fq[i]/(i^2+1), Fq6 = Fq2[v]/(v^3-(9+i)), and
    Fq12 = Fq6[w]/(w^2-v). Coefficients are stored low degree first.
    This module does not dispatch the address-8 precompile. *)
Module Bn254Tower.
  Module Fq2 := Bn254Pairing.Fq2.

  Module Fq6.
    Record t : Set := {
      c0 : Fq2.t;
      c1 : Fq2.t;
      c2 : Fq2.t;
    }.

    Definition make (a0 a1 a2 : Fq2.t) : t :=
      {| c0 := a0; c1 := a1; c2 := a2 |}.

    Definition zero : t := make Fq2.zero Fq2.zero Fq2.zero.

    Definition one : t := make Fq2.one Fq2.zero Fq2.zero.

    Definition v : t := make Fq2.zero Fq2.one Fq2.zero.

    Definition eqb (left right : t) : bool :=
      Fq2.eqb left.(c0) right.(c0) &&
      Fq2.eqb left.(c1) right.(c1) &&
      Fq2.eqb left.(c2) right.(c2).

    Definition is_zero (value : t) : bool := eqb value zero.

    Definition is_one (value : t) : bool := eqb value one.

    Definition add (left right : t) : t :=
      make (Fq2.add left.(c0) right.(c0))
        (Fq2.add left.(c1) right.(c1))
        (Fq2.add left.(c2) right.(c2)).

    Definition sub (left right : t) : t :=
      make (Fq2.sub left.(c0) right.(c0))
        (Fq2.sub left.(c1) right.(c1))
        (Fq2.sub left.(c2) right.(c2)).

    Definition negate (value : t) : t :=
      make (Fq2.negate value.(c0))
        (Fq2.negate value.(c1))
        (Fq2.negate value.(c2)).

    Definition mul_v (value : t) : t :=
      make (Fq2.mul Fq2.xi value.(c2)) value.(c0) value.(c1).

    Definition mul_fq2 (value : t) (scalar : Fq2.t) : t :=
      make (Fq2.mul value.(c0) scalar)
        (Fq2.mul value.(c1) scalar)
        (Fq2.mul value.(c2) scalar).

    Definition mul (left right : t) : t :=
      let a0 := left.(c0) in
      let a1 := left.(c1) in
      let a2 := left.(c2) in
      let b0 := right.(c0) in
      let b1 := right.(c1) in
      let b2 := right.(c2) in
      make
        (Fq2.add (Fq2.mul a0 b0)
          (Fq2.mul Fq2.xi
            (Fq2.add (Fq2.mul a1 b2) (Fq2.mul a2 b1))))
        (Fq2.add (Fq2.add (Fq2.mul a0 b1) (Fq2.mul a1 b0))
          (Fq2.mul Fq2.xi (Fq2.mul a2 b2)))
        (Fq2.add (Fq2.add (Fq2.mul a0 b2) (Fq2.mul a1 b1))
          (Fq2.mul a2 b0)).

    Definition square (value : t) : t := mul value value.

    (** Adjugate of a0 + a1*v + a2*v^2, with v^3 = 9+i. *)
    Definition inverse (value : t) : t :=
      let a0 := value.(c0) in
      let a1 := value.(c1) in
      let a2 := value.(c2) in
      let t0 := Fq2.sub (Fq2.square a0)
        (Fq2.mul Fq2.xi (Fq2.mul a1 a2)) in
      let t1 := Fq2.sub (Fq2.mul Fq2.xi (Fq2.square a2))
        (Fq2.mul a0 a1) in
      let t2 := Fq2.sub (Fq2.square a1) (Fq2.mul a0 a2) in
      let denominator := Fq2.add (Fq2.mul a0 t0)
        (Fq2.mul Fq2.xi
          (Fq2.add (Fq2.mul a2 t1) (Fq2.mul a1 t2))) in
      mul_fq2 (make t0 t1 t2) (Fq2.inverse denominator).
  End Fq6.

  Module Fq12.
    Record t : Set := {
      c0 : Fq6.t;
      c1 : Fq6.t;
    }.

    Definition make (a0 a1 : Fq6.t) : t :=
      {| c0 := a0; c1 := a1 |}.

    Definition zero : t := make Fq6.zero Fq6.zero.

    Definition one : t := make Fq6.one Fq6.zero.

    Definition w : t := make Fq6.zero Fq6.one.

    Definition eqb (left right : t) : bool :=
      Fq6.eqb left.(c0) right.(c0) && Fq6.eqb left.(c1) right.(c1).

    Definition is_zero (value : t) : bool := eqb value zero.

    Definition is_one (value : t) : bool := eqb value one.

    Definition add (left right : t) : t :=
      make (Fq6.add left.(c0) right.(c0))
        (Fq6.add left.(c1) right.(c1)).

    Definition sub (left right : t) : t :=
      make (Fq6.sub left.(c0) right.(c0))
        (Fq6.sub left.(c1) right.(c1)).

    Definition negate (value : t) : t :=
      make (Fq6.negate value.(c0)) (Fq6.negate value.(c1)).

    Definition conjugate (value : t) : t :=
      make value.(c0) (Fq6.negate value.(c1)).

    Definition mul (left right : t) : t :=
      let a0 := left.(c0) in
      let a1 := left.(c1) in
      let b0 := right.(c0) in
      let b1 := right.(c1) in
      make (Fq6.add (Fq6.mul a0 b0)
        (Fq6.mul_v (Fq6.mul a1 b1)))
        (Fq6.add (Fq6.mul a0 b1) (Fq6.mul a1 b0)).

    Definition square (value : t) : t := mul value value.

    Definition inverse (value : t) : t :=
      let a0 := value.(c0) in
      let a1 := value.(c1) in
      let denominator := Fq6.sub (Fq6.square a0)
        (Fq6.mul_v (Fq6.square a1)) in
      let reciprocal := Fq6.inverse denominator in
      make (Fq6.mul a0 reciprocal)
        (Fq6.negate (Fq6.mul a1 reciprocal)).

    Fixpoint pow_positive (base : t) (exponent : positive) : t :=
      match exponent with
      | xH => base
      | xO rest =>
          let half := pow_positive base rest in
          square half
      | xI rest =>
          let half := pow_positive base rest in
          mul (square half) base
      end.

    Definition pow (base : t) (exponent : Z) : t :=
      match exponent with
      | Zpos positive_exponent => pow_positive base positive_exponent
      | Z0 | Zneg _ => one
      end.
  End Fq12.
End Bn254Tower.
