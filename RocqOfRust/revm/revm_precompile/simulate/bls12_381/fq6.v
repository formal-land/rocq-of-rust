Require Import revm.revm_precompile.simulate.bls12_381.arkworks.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.
From Stdlib Require Import Bool List ZArith.

Import ListNotations.
Open Scope Z_scope.

(** Canonical-residue specialization of ark-ff 0.5.0 fp6_3over2 and
    ark-bls12-381 fields/fq6.rs. The tower satisfies v^3 = 1 + i.
    This does not establish correspondence with Montgomery arithmetic. *)
Module Fq6.
  Import arkworks.

  Record t : Set := { c0 : Fq2.t; c1 : Fq2.t; c2 : Fq2.t }.

  Module Valid.
    Definition t (value : t) : Prop :=
      Fq2.Valid.t value.(c0) /\ Fq2.Valid.t value.(c1) /\ Fq2.Valid.t value.(c2).

    Arguments t /.
  End Valid.

  Definition ZERO : t := {| c0 := Fq2.ZERO; c1 := Fq2.ZERO; c2 := Fq2.ZERO |}.

  Definition ONE : t := {| c0 := Fq2.ONE; c1 := Fq2.ZERO; c2 := Fq2.ZERO |}.

  Definition add (left right : t) : t :=
    {| c0 := Fq2.add left.(c0) right.(c0);
       c1 := Fq2.add left.(c1) right.(c1);
       c2 := Fq2.add left.(c2) right.(c2) |}.

  Definition sub (left right : t) : t :=
    {| c0 := Fq2.sub left.(c0) right.(c0);
       c1 := Fq2.sub left.(c1) right.(c1);
       c2 := Fq2.sub left.(c2) right.(c2) |}.

  Definition mul_fp2_by_nonresidue (value : Fq2.t) : Fq2.t :=
    {| Fq2.c0 := Fq.sub value.(Fq2.c0) value.(Fq2.c1);
       Fq2.c1 := Fq.add value.(Fq2.c0) value.(Fq2.c1) |}.

  Definition mul (left right : t) : t :=
    let v0 := Fq2.mul left.(c0) right.(c0) in
    let v1 := Fq2.mul left.(c1) right.(c1) in
    let v2 := Fq2.mul left.(c2) right.(c2) in
    {| c0 := Fq2.add v0 (mul_fp2_by_nonresidue
         (Fq2.sub (Fq2.sub (Fq2.mul (Fq2.add left.(c1) left.(c2))
           (Fq2.add right.(c1) right.(c2))) v1) v2));
       c1 := Fq2.add (Fq2.sub (Fq2.sub
         (Fq2.mul (Fq2.add left.(c0) left.(c1)) (Fq2.add right.(c0) right.(c1))) v0) v1)
         (mul_fp2_by_nonresidue v2);
       c2 := Fq2.add (Fq2.sub (Fq2.sub
         (Fq2.mul (Fq2.add left.(c0) left.(c2)) (Fq2.add right.(c0) right.(c2))) v0) v2) v1 |}.

  Definition square (value : t) : t := mul value value.

  Definition eq (left right : t) : bool :=
    Fq2.eq left.(c0) right.(c0) && Fq2.eq left.(c1) right.(c1) &&
    Fq2.eq left.(c2) right.(c2).

  Definition is_zero (value : t) : bool := eq value ZERO.

  Definition mul_by_nonresidue (value : t) : t :=
    {| c0 := mul_fp2_by_nonresidue value.(c2); c1 := value.(c0); c2 := value.(c1) |}.

  Definition inverse (value : t) : option t :=
    let s0 := Fq2.sub (Fq2.square value.(c0))
      (mul_fp2_by_nonresidue (Fq2.mul value.(c1) value.(c2))) in
    let s1 := Fq2.sub (mul_fp2_by_nonresidue (Fq2.square value.(c2)))
      (Fq2.mul value.(c0) value.(c1)) in
    let s2 := Fq2.sub (Fq2.square value.(c1)) (Fq2.mul value.(c0) value.(c2)) in
    match Fq2.inverse (Fq2.add (Fq2.mul value.(c0) s0)
      (mul_fp2_by_nonresidue (Fq2.add (Fq2.mul value.(c2) s1) (Fq2.mul value.(c1) s2)))) with
    | None => None
    | Some inverse => Some
      {| c0 := Fq2.mul inverse s0; c1 := Fq2.mul inverse s1; c2 := Fq2.mul inverse s2 |}
    end.

  Definition fp2_frobenius_map (value : Fq2.t) (power : usize) : Fq2.t :=
    if Z.odd power.(Integer.value) then
      {| Fq2.c0 := value.(Fq2.c0); Fq2.c1 := Fq.sub Fq.ZERO value.(Fq2.c1) |}
    else value.

  Definition FROBENIUS_COEFF_FP6_C1 : list Fq2.t := [
    {| Fq2.c0 := Fq.ONE; Fq2.c1 := Fq.ZERO |};
    {| Fq2.c0 := Fq.ZERO; Fq2.c1 := {| Fq.repr := {| Uint.value := 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436 |} |} |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350 |} |}; Fq2.c1 := Fq.ZERO |};
    {| Fq2.c0 := Fq.ZERO; Fq2.c1 := Fq.ONE |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436 |} |}; Fq2.c1 := Fq.ZERO |};
    {| Fq2.c0 := Fq.ZERO; Fq2.c1 := {| Fq.repr := {| Uint.value := 793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350 |} |} |}
  ].

  Definition FROBENIUS_COEFF_FP6_C2 : list Fq2.t := [
    {| Fq2.c0 := Fq.ONE; Fq2.c1 := Fq.ZERO |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437 |} |}; Fq2.c1 := Fq.ZERO |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436 |} |}; Fq2.c1 := Fq.ZERO |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786 |} |}; Fq2.c1 := Fq.ZERO |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350 |} |}; Fq2.c1 := Fq.ZERO |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620351 |} |}; Fq2.c1 := Fq.ZERO |}
  ].

  Definition frobenius_map (value : t) (power : usize) : t :=
    let index := Z.to_nat (power.(Integer.value) mod 6) in
    {| c0 := fp2_frobenius_map value.(c0) power;
       c1 := Fq2.mul (fp2_frobenius_map value.(c1) power)
         (List.nth index FROBENIUS_COEFF_FP6_C1 Fq2.ONE);
       c2 := Fq2.mul (fp2_frobenius_map value.(c2) power)
         (List.nth index FROBENIUS_COEFF_FP6_C2 Fq2.ONE) |}.
End Fq6.
