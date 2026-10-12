From Stdlib Require Import Bool List ZArith.
Require Import revm.revm_precompile.simulate.modexp.
Import ListNotations.
Open Scope Z_scope.

(** Executable G1 operations for revm_precompile/bn254.rs and its arkworks
    provider. G1 has cofactor one. Jacobian arithmetic follows the same a=0
    formulas as the local Secp256k1 implementation, with independent field and
    curve constants; no native-provider correspondence theorem is claimed. *)
Module Bn254.
  Definition field_modulus : Z :=
    21888242871839275222246405745257275088696311157297823662689037894645226208583.
  Definition scalar_modulus : Z :=
    21888242871839275222246405745257275088548364400416034343698204186575808495617.
  Module Field.
    Definition add (left right : Z) : Z := (left + right) mod field_modulus.
    Definition sub (left right : Z) : Z := (left - right) mod field_modulus.
    Definition mul (left right : Z) : Z := (left * right) mod field_modulus.
    Definition square (value : Z) : Z := mul value value.
    Definition negate (value : Z) : Z := (- value) mod field_modulus.
    Definition inverse (value : Z) : Z :=
      Modexp.pow_mod value (field_modulus - 2) field_modulus.
  End Field.

  Module Point.
    Record t : Set := {
      x : Z;
      y : Z;
      z : Z;
    }.

    Definition infinity : t := {| x := 0; y := 1; z := 0 |}.
    Definition is_infinity (point : t) : bool := point.(z) =? 0.
    Definition of_affine (affine_x affine_y : Z) : t :=
      {| x := affine_x mod field_modulus;
         y := affine_y mod field_modulus;
         z := 1 |}.

    Definition to_affine (point : t) : option (Z * Z) :=
      if is_infinity point then None else
      let inverse_z := Field.inverse point.(z) in
      let inverse_z_squared := Field.square inverse_z in
      let inverse_z_cubed := Field.mul inverse_z_squared inverse_z in
      Some (Field.mul point.(x) inverse_z_squared,
        Field.mul point.(y) inverse_z_cubed).

    Definition on_curve (affine_x affine_y : Z) : bool :=
      Field.square affine_y =?
        Field.add (Field.mul (Field.square affine_x) affine_x) 3.

    Definition double (point : t) : t :=
      if is_infinity point || (point.(y) =? 0) then infinity else
      let xx := Field.square point.(x) in
      let yy := Field.square point.(y) in
      let yyyy := Field.square yy in
      let zz := Field.square point.(z) in
      let s := Field.mul 2
        (Field.sub (Field.sub (Field.square (Field.add point.(x) yy)) xx) yyyy) in
      let m := Field.mul 3 xx in
      let x3 := Field.sub (Field.square m) (Field.mul 2 s) in
      let y3 := Field.sub (Field.mul m (Field.sub s x3)) (Field.mul 8 yyyy) in
      let z3 := Field.sub (Field.sub (Field.square (Field.add point.(y) point.(z))) yy) zz in
      {| x := x3; y := y3; z := z3 |}.

    Definition add (left right : t) : t :=
      if is_infinity left then right else
      if is_infinity right then left else
      let z1z1 := Field.square left.(z) in
      let z2z2 := Field.square right.(z) in
      let u1 := Field.mul left.(x) z2z2 in
      let u2 := Field.mul right.(x) z1z1 in
      let s1 := Field.mul (Field.mul left.(y) right.(z)) z2z2 in
      let s2 := Field.mul (Field.mul right.(y) left.(z)) z1z1 in
      if u1 =? u2 then
        if s1 =? s2 then double left else infinity
      else
        let h := Field.sub u2 u1 in
        let i := Field.square (Field.mul 2 h) in
        let j := Field.mul h i in
        let r := Field.mul 2 (Field.sub s2 s1) in
        let v := Field.mul u1 i in
        let x3 := Field.sub (Field.sub (Field.square r) j) (Field.mul 2 v) in
        let y3 := Field.sub (Field.mul r (Field.sub v x3))
          (Field.mul 2 (Field.mul s1 j)) in
        let z3 := Field.mul
          (Field.sub (Field.sub (Field.square (Field.add left.(z) right.(z))) z1z1) z2z2) h in
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
  End Point.


  Module Error.
    Inductive t : Set := FieldPointNotAMember | AffineGFailedToCreate.
  End Error.
  Module Decoded.
    Inductive t : Set := Valid (point : Point.t) | Invalid (error : Error.t).
  End Decoded.
  Definition decode_point (input : list Z) : Decoded.t :=
    let x := Modexp.decode_be (List.firstn 32 input) in
    let y := Modexp.decode_be (List.firstn 32 (List.skipn 32 input)) in
    if negb ((0 <=? x) && (x <? field_modulus) &&
      (0 <=? y) && (y <? field_modulus)) then Decoded.Invalid Error.FieldPointNotAMember else
    if (x =? 0) && (y =? 0) then Decoded.Valid Point.infinity else
    if Point.on_curve x y then Decoded.Valid (Point.of_affine x y)
    else Decoded.Invalid Error.AffineGFailedToCreate.
  Definition encode_point (point : Point.t) : list Z :=
    match Point.to_affine point with
    | None => List.repeat 0 64
    | Some (x, y) => Modexp.encode_be 32 x ++ Modexp.encode_be 32 y
    end.
  Module Result.
    Inductive t : Set :=
    | Success (cost : Z) (output : list Z)
    | OutOfGas | InvalidPoint (error : Error.t).
  End Result.
  Definition run_add (input : list Z) (gas_cost gas_limit : Z) : Result.t :=
    if gas_limit <? gas_cost then Result.OutOfGas else
    let input := Modexp.read_padded input 0 128 in
    match decode_point (List.firstn 64 input) with
    | Decoded.Invalid error => Result.InvalidPoint error
    | Decoded.Valid point_l =>
      match decode_point (List.skipn 64 input) with
      | Decoded.Invalid error => Result.InvalidPoint error
      | Decoded.Valid point_r => Result.Success gas_cost (encode_point (Point.add point_l point_r))
      end
    end.
  Definition run_mul (input : list Z) (gas_cost gas_limit : Z) : Result.t :=
    if gas_limit <? gas_cost then Result.OutOfGas else
    let input := Modexp.read_padded input 0 96 in
    match decode_point (List.firstn 64 input) with
    | Decoded.Invalid error => Result.InvalidPoint error
    | Decoded.Valid point =>
      let scalar := Modexp.decode_be (List.skipn 64 input) mod scalar_modulus in
      Result.Success gas_cost (encode_point (Point.mul point scalar))
    end.
End Bn254.
