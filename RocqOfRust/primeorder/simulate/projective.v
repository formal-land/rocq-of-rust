From Stdlib Require Import Bool ZArith.

Require Import p256.simulate.arithmetic.
Require Import p256.simulate.arithmetic.field.
Require Import p256.simulate.arithmetic.scalar.
Require Import primeorder.simulate.affine.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

(** P256 specialization of primeorder/projective.rs. Jacobian coordinates give
    executable group operations. Rust uses complete projective formulas; these
    formulas and their exceptional branches have no native correspondence proof. *)
Module ProjectivePoint.
  Record t : Set := { x : FieldElement.t; y : FieldElement.t; z : FieldElement.t }.

  Definition IDENTITY : t :=
    {| x := FieldElement.ZERO; y := FieldElement.ONE; z := FieldElement.ZERO |}.

  Definition is_identity (point : t) : bool := FieldElement.is_zero point.(z).

  Definition from_affine (point : AffinePoint.t) : t :=
    {| x := point.(AffinePoint.x); y := point.(AffinePoint.y); z := FieldElement.ONE |}.

  Definition GENERATOR : t :=
    from_affine {| AffinePoint.x := fst NistP256.GENERATOR;
                   AffinePoint.y := snd NistP256.GENERATOR |}.

  Definition to_affine (point : t) : option AffinePoint.t :=
    match FieldElement.invert point.(z) with
    | None => None
    | Some inverse =>
      let squared := FieldElement.square inverse in
      Some {| AffinePoint.x := FieldElement.mul point.(x) squared;
              AffinePoint.y := FieldElement.mul point.(y) (FieldElement.mul squared inverse) |}
    end.

  Definition double (point : t) : t :=
    if is_identity point || FieldElement.is_zero point.(y) then IDENTITY else
    let xx := FieldElement.square point.(x) in
    let yy := FieldElement.square point.(y) in
    let yyyy := FieldElement.square yy in
    let zz := FieldElement.square point.(z) in
    let half_s := FieldElement.sub
      (FieldElement.sub (FieldElement.square (FieldElement.add point.(x) yy)) xx) yyyy in
    let s := FieldElement.add half_s half_s in
    let m := FieldElement.add (FieldElement.add xx (FieldElement.add xx xx))
      (FieldElement.mul NistP256.EQUATION_A (FieldElement.square zz)) in
    let x3 := FieldElement.sub (FieldElement.square m) (FieldElement.add s s) in
    let twice_yyyy := FieldElement.add yyyy yyyy in
    let four_yyyy := FieldElement.add twice_yyyy twice_yyyy in
    let y3 := FieldElement.sub (FieldElement.mul m (FieldElement.sub s x3))
      (FieldElement.add four_yyyy four_yyyy) in
    let z3 := FieldElement.sub
      (FieldElement.sub (FieldElement.square (FieldElement.add point.(y) point.(z))) yy) zz in
    {| x := x3; y := y3; z := z3 |}.

  Definition add (left right : t) : t :=
    if is_identity left then right else
    if is_identity right then left else
    let z1z1 := FieldElement.square left.(z) in
    let z2z2 := FieldElement.square right.(z) in
    let u1 := FieldElement.mul left.(x) z2z2 in
    let u2 := FieldElement.mul right.(x) z1z1 in
    let s1 := FieldElement.mul (FieldElement.mul left.(y) right.(z)) z2z2 in
    let s2 := FieldElement.mul (FieldElement.mul right.(y) left.(z)) z1z1 in
    if FieldElement.eq u1 u2 then
      if FieldElement.eq s1 s2 then double left else IDENTITY
    else
      let h := FieldElement.sub u2 u1 in
      let i := FieldElement.square (FieldElement.add h h) in
      let j := FieldElement.mul h i in
      let half_r := FieldElement.sub s2 s1 in
      let r := FieldElement.add half_r half_r in
      let v := FieldElement.mul u1 i in
      let x3 := FieldElement.sub (FieldElement.sub (FieldElement.square r) j)
        (FieldElement.add v v) in
      let s1j := FieldElement.mul s1 j in
      let y3 := FieldElement.sub (FieldElement.mul r (FieldElement.sub v x3))
        (FieldElement.add s1j s1j) in
      let z3 := FieldElement.mul
        (FieldElement.sub (FieldElement.sub
          (FieldElement.square (FieldElement.add left.(z) right.(z))) z1z1) z2z2) h in
      {| x := x3; y := y3; z := z3 |}.

  Definition mul (point : t) (scalar : Scalar.t) : t :=
    let fix loop (bits : positive) : t :=
      match bits with
      | xH => point
      | xO rest => double (loop rest)
      | xI rest => add point (double (loop rest))
      end in
    match scalar.(Scalar.repr).(Uint.value) with
    | Zpos bits => loop bits
    | _ => IDENTITY
    end.

  Definition lincomb (left : t) (left_scalar : Scalar.t)
      (right : t) (right_scalar : Scalar.t) : t :=
    add (mul left left_scalar) (mul right right_scalar).
End ProjectivePoint.
