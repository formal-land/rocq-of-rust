From Stdlib Require Import Bool List ZArith.

Require Import revm.revm_precompile.simulate.bn254.
Require Import revm.revm_precompile.simulate.modexp.

Import ListNotations.
Open Scope Z_scope.

(** Field and G2 input validation for the BN254 pairing precompile.
    Computation checks do not prove equivalence with the native provider. *)
Module Bn254Pairing.
  Module Fq2.
    (** a0 + a1 * i, where i^2 = -1. This order differs from the EVM wire
        encoding, which places the imaginary coefficient first. *)
    Record t : Set := {
      real : Z;
      imag : Z;
    }.

    Definition make (a0 a1 : Z) : t :=
      {| real := a0 mod Bn254.field_modulus;
         imag := a1 mod Bn254.field_modulus |}.
    Definition zero : t := make 0 0.
    Definition one : t := make 1 0.
    Definition of_z (value : Z) : t := make value 0.
    Definition xi : t := make 9 1.
    Definition eqb (left right : t) : bool :=
      (left.(real) =? right.(real)) && (left.(imag) =? right.(imag)).
    Definition is_zero (value : t) : bool := eqb value zero.
    Definition add (left right : t) : t :=
      make (left.(real) + right.(real)) (left.(imag) + right.(imag)).
    Definition sub (left right : t) : t :=
      make (left.(real) - right.(real)) (left.(imag) - right.(imag)).
    Definition negate (value : t) : t :=
      make (- value.(real)) (- value.(imag)).
    Definition mul (left right : t) : t :=
      make (left.(real) * right.(real) - left.(imag) * right.(imag))
        (left.(real) * right.(imag) + left.(imag) * right.(real)).
    Definition square (value : t) : t := mul value value.
    Definition mul_z (value : t) (scalar : Z) : t := mul value (of_z scalar).
    Definition inverse (value : t) : t :=
      let denominator := Bn254.Field.add
        (Bn254.Field.square value.(real))
        (Bn254.Field.square value.(imag)) in
      let reciprocal := Bn254.Field.inverse denominator in
      make (value.(real) * reciprocal) (- value.(imag) * reciprocal).
  End Fq2.

  Module G2.
    Record t : Set := {
      x : Fq2.t;
      y : Fq2.t;
      z : Fq2.t;
    }.

    Definition infinity : t :=
      {| x := Fq2.zero; y := Fq2.one; z := Fq2.zero |}.
    Definition is_infinity (point : t) : bool := Fq2.is_zero point.(z).
    Definition of_affine (affine_x affine_y : Fq2.t) : t :=
      {| x := affine_x; y := affine_y; z := Fq2.one |}.

    (** 3 / (9 + i), in normal residues. The two coefficients can also be
        checked by Fq2.mul twist_b Fq2.xi = Fq2.of_z 3. *)
    Definition twist_b : Fq2.t := Fq2.make
      19485874751759354771024239261021720505790618469301721065564631296452457478373
      266929791119991161246907387137283842545076965332900288569378510910307636690.

    Definition on_curve (affine_x affine_y : Fq2.t) : bool :=
      Fq2.eqb (Fq2.square affine_y)
        (Fq2.add (Fq2.mul (Fq2.square affine_x) affine_x) twist_b).

    Definition double (point : t) : t :=
      if is_infinity point || Fq2.is_zero point.(y) then infinity else
      let xx := Fq2.square point.(x) in
      let yy := Fq2.square point.(y) in
      let yyyy := Fq2.square yy in
      let zz := Fq2.square point.(z) in
      let s := Fq2.mul_z
        (Fq2.sub (Fq2.sub (Fq2.square (Fq2.add point.(x) yy)) xx) yyyy) 2 in
      let m := Fq2.mul_z xx 3 in
      let x3 := Fq2.sub (Fq2.square m) (Fq2.mul_z s 2) in
      let y3 := Fq2.sub (Fq2.mul m (Fq2.sub s x3)) (Fq2.mul_z yyyy 8) in
      let z3 := Fq2.sub (Fq2.sub (Fq2.square (Fq2.add point.(y) point.(z))) yy) zz in
      {| x := x3; y := y3; z := z3 |}.

    Definition add (left right : t) : t :=
      if is_infinity left then right else
      if is_infinity right then left else
      let z1z1 := Fq2.square left.(z) in
      let z2z2 := Fq2.square right.(z) in
      let u1 := Fq2.mul left.(x) z2z2 in
      let u2 := Fq2.mul right.(x) z1z1 in
      let s1 := Fq2.mul (Fq2.mul left.(y) right.(z)) z2z2 in
      let s2 := Fq2.mul (Fq2.mul right.(y) left.(z)) z1z1 in
      if Fq2.eqb u1 u2 then
        if Fq2.eqb s1 s2 then double left else infinity
      else
        let h := Fq2.sub u2 u1 in
        let i := Fq2.square (Fq2.mul_z h 2) in
        let j := Fq2.mul h i in
        let r := Fq2.mul_z (Fq2.sub s2 s1) 2 in
        let v := Fq2.mul u1 i in
        let x3 := Fq2.sub (Fq2.sub (Fq2.square r) j) (Fq2.mul_z v 2) in
        let y3 := Fq2.sub (Fq2.mul r (Fq2.sub v x3))
          (Fq2.mul_z (Fq2.mul s1 j) 2) in
        let z3 := Fq2.mul
          (Fq2.sub (Fq2.sub (Fq2.square (Fq2.add left.(z) right.(z))) z1z1) z2z2) h in
        {| x := x3; y := y3; z := z3 |}.

    Fixpoint mul_positive (point : t) (scalar : positive) : t :=
      match scalar with
      | xH => point
      | xO rest => double (mul_positive point rest)
      | xI rest => add point (double (mul_positive point rest))
      end.

    Definition mul (point : t) (scalar : Z) : t :=
      match scalar with
      | Zpos positive_scalar => mul_positive point positive_scalar
      | Z0 | Zneg _ => infinity
      end.
  End G2.

  Module Error.
    Inductive t : Set :=
    | InvalidLength
    | FieldPointNotAMember
    | AffineGFailedToCreate.
  End Error.
  Module Decoded.
    Inductive t : Set :=
    | Valid (point : G2.t)
    | Invalid (error : Error.t).
  End Decoded.

  Definition valid_byte (byte : Z) : bool :=
    (0 <=? byte) && (byte <? 256).

  (** Exact 128-byte G2 input, in x.imag, x.real, y.imag, y.real order. *)
  Definition decode_g2 (input : list Z) : Decoded.t :=
    if negb (Nat.eqb (List.length input) 128) then
      Decoded.Invalid Error.InvalidLength else
    if negb (List.forallb valid_byte input) then
      Decoded.Invalid Error.FieldPointNotAMember else
    let x_imag := Modexp.decode_be (List.firstn 32 input) in
    let x_real := Modexp.decode_be (List.firstn 32 (List.skipn 32 input)) in
    let y_imag := Modexp.decode_be (List.firstn 32 (List.skipn 64 input)) in
    let y_real := Modexp.decode_be (List.skipn 96 input) in
    if negb ((x_imag <? Bn254.field_modulus) &&
      (x_real <? Bn254.field_modulus) &&
      (y_imag <? Bn254.field_modulus) &&
      (y_real <? Bn254.field_modulus)) then
      Decoded.Invalid Error.FieldPointNotAMember else
    if (x_imag =? 0) && (x_real =? 0) &&
       (y_imag =? 0) && (y_real =? 0) then
      Decoded.Valid G2.infinity else
    let x := Fq2.make x_real x_imag in
    let y := Fq2.make y_real y_imag in
    if negb (G2.on_curve x y) then
      Decoded.Invalid Error.AffineGFailedToCreate else
    let point := G2.of_affine x y in
    if G2.is_infinity (G2.mul point Bn254.scalar_modulus) then
      Decoded.Valid point
    else Decoded.Invalid Error.AffineGFailedToCreate.
End Bn254Pairing.
