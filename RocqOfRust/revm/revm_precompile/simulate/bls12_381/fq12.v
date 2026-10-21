Require Import revm.revm_precompile.simulate.bls12_381.arkworks.
Require Import revm.revm_precompile.simulate.bls12_381.fq6.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.
From Stdlib Require Import Bool List ZArith.

Import ListNotations.
Open Scope Z_scope.


(** Canonical-residue specialization of ark-ff 0.5.0 fp12_2over3over2
    and ark-bls12-381 fields/fq12.rs, with w^2 = v. *)
Module Fq12.
  Import arkworks.

  Record t : Set := { c0 : Fq6.t; c1 : Fq6.t }.

  Module Valid.
    Definition t (value : t) : Prop := Fq6.Valid.t value.(c0) /\ Fq6.Valid.t value.(c1).

    Arguments t /.
  End Valid.

  Definition ZERO : t := {| c0 := Fq6.ZERO; c1 := Fq6.ZERO |}.

  Definition ONE : t := {| c0 := Fq6.ONE; c1 := Fq6.ZERO |}.

  Definition add (left right : t) : t :=
    {| c0 := Fq6.add left.(c0) right.(c0); c1 := Fq6.add left.(c1) right.(c1) |}.

  Definition sub (left right : t) : t :=
    {| c0 := Fq6.sub left.(c0) right.(c0); c1 := Fq6.sub left.(c1) right.(c1) |}.

  Definition mul (left right : t) : t :=
    let v0 := Fq6.mul left.(c0) right.(c0) in
    let v1 := Fq6.mul left.(c1) right.(c1) in
    {| c0 := Fq6.add v0 (Fq6.mul_by_nonresidue v1);
       c1 := Fq6.sub (Fq6.sub
         (Fq6.mul (Fq6.add left.(c0) left.(c1)) (Fq6.add right.(c0) right.(c1))) v0) v1 |}.

  Definition square (value : t) : t := mul value value.

  Definition eq (left right : t) : bool :=
    Fq6.eq left.(c0) right.(c0) && Fq6.eq left.(c1) right.(c1).

  Definition is_zero (value : t) : bool := eq value ZERO.

  Definition conjugate (value : t) : t :=
    {| c0 := value.(c0); c1 := Fq6.sub Fq6.ZERO value.(c1) |}.

  Definition inverse (value : t) : option t :=
    match Fq6.inverse (Fq6.sub (Fq6.square value.(c0))
      (Fq6.mul_by_nonresidue (Fq6.square value.(c1)))) with
    | None => None
    | Some inverse => Some
      {| c0 := Fq6.mul value.(c0) inverse;
         c1 := Fq6.sub Fq6.ZERO (Fq6.mul value.(c1) inverse) |}
    end.

  Definition mul_by_014 (value : t) (c0 c1 c4 : Fq2.t) : t :=
    mul value {| c0 := {| Fq6.c0 := c0; Fq6.c1 := c1; Fq6.c2 := Fq2.ZERO |};
                 c1 := {| Fq6.c0 := Fq2.ZERO; Fq6.c1 := c4; Fq6.c2 := Fq2.ZERO |} |}.

  Definition FROBENIUS_COEFF_FP12_C1 : list Fq2.t := [
    {| Fq2.c0 := Fq.ONE; Fq2.c1 := Fq.ZERO |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 3850754370037169011952147076051364057158807420970682438676050522613628423219637725072182697113062777891589506424760 |} |}; Fq2.c1 := {| Fq.repr := {| Uint.value := 151655185184498381465642749684540099398075398968325446656007613510403227271200139370504932015952886146304766135027 |} |} |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620351 |} |}; Fq2.c1 := Fq.ZERO |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530 |} |}; Fq2.c1 := {| Fq.repr := {| Uint.value := 1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257 |} |} |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350 |} |}; Fq2.c1 := Fq.ZERO |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 3125332594171059424908108096204648978570118281977575435832422631601824034463382777937621250592425535493320683825557 |} |}; Fq2.c1 := {| Fq.repr := {| Uint.value := 877076961050607968509681729531255177986764537961432449499635504522207616027455086505066378536590128544573588734230 |} |} |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786 |} |}; Fq2.c1 := Fq.ZERO |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 151655185184498381465642749684540099398075398968325446656007613510403227271200139370504932015952886146304766135027 |} |}; Fq2.c1 := {| Fq.repr := {| Uint.value := 3850754370037169011952147076051364057158807420970682438676050522613628423219637725072182697113062777891589506424760 |} |} |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436 |} |}; Fq2.c1 := Fq.ZERO |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257 |} |}; Fq2.c1 := {| Fq.repr := {| Uint.value := 2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530 |} |} |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437 |} |}; Fq2.c1 := Fq.ZERO |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 877076961050607968509681729531255177986764537961432449499635504522207616027455086505066378536590128544573588734230 |} |}; Fq2.c1 := {| Fq.repr := {| Uint.value := 3125332594171059424908108096204648978570118281977575435832422631601824034463382777937621250592425535493320683825557 |} |} |}
  ].

  Definition frobenius_map (value : t) (power : usize) : t :=
    let coefficient := List.nth (Z.to_nat (power.(Integer.value) mod 12))
      FROBENIUS_COEFF_FP12_C1 Fq2.ONE in
    let c1 := Fq6.frobenius_map value.(c1) power in
    {| c0 := Fq6.frobenius_map value.(c0) power;
       c1 := {| Fq6.c0 := Fq2.mul c1.(Fq6.c0) coefficient;
                Fq6.c1 := Fq2.mul c1.(Fq6.c1) coefficient;
                Fq6.c2 := Fq2.mul c1.(Fq6.c2) coefficient |} |}.
End Fq12.
