From Stdlib Require Import Bool List ZArith.

Require Import alloy_primitives.utils.simulate.keccak256.
Require Import revm.revm_precompile.simulate.modexp.

Import ListNotations.
Open Scope Z_scope.

(** Executable recovery for revm_precompile/secp256k1.rs. Jacobian formulas
    follow the existing Rocq Weierstrass implementation. These definitions do
    not establish curve arithmetic or native-provider correspondence. *)
Module Secp256k1.
  Definition field_modulus : Z := 2 ^ 256 - 2 ^ 32 - 977.
  Definition scalar_modulus : Z :=
    115792089237316195423570985008687907852837564279074904382605163141518161494337.
  Definition generator_x : Z :=
    55066263022277343669578718895168534326250603453777594175500187360389116729240.
  Definition generator_y : Z :=
    32670510020758816978083085130507043184471273380659243275938904335757337482424.

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
        Field.add (Field.mul (Field.square affine_x) affine_x) 7.

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

  Definition generator : Point.t := Point.of_affine generator_x generator_y.

  Definition scalar_valid (scalar : Z) : bool :=
    (0 <? scalar) && (scalar <? scalar_modulus).

  Definition recover_public_key (message_hash r s recovery_id : Z) : option (Z * Z) :=
    if negb (((recovery_id =? 0) || (recovery_id =? 1)) &&
      scalar_valid r && scalar_valid s) then None else
    let rhs := Field.add (Field.mul (Field.square r) r) 7 in
    let root := Modexp.pow_mod rhs ((field_modulus + 1) / 4) field_modulus in
    if negb (Field.square root =? rhs) then None else
    let want_odd := recovery_id =? 1 in
    let y := if Bool.eqb (Z.odd root) want_odd then root else Field.negate root in
    let recovered_point := Point.of_affine r y in
    let r_inverse := Modexp.pow_mod r (scalar_modulus - 2) scalar_modulus in
    let u1 := (- message_hash * r_inverse) mod scalar_modulus in
    let u2 := (s * r_inverse) mod scalar_modulus in
    Point.to_affine (Point.add (Point.mul generator u1) (Point.mul recovered_point u2)).

  Definition address (public_key : Z * Z) : list Z :=
    let '(x, y) := public_key in
    let digest := Keccak256.hash (Modexp.encode_be 32 x ++ Modexp.encode_be 32 y) in
    List.repeat 0 12 ++ List.firstn 20 (List.skipn 12 digest).

  Definition recover (message_hash r s recovery_id : Z) : option (list Z) :=
    option_map address (recover_public_key message_hash r s recovery_id).

  Definition output (input : list Z) : list Z :=
    let padded := Modexp.read_padded input 0 128 in
    let v := List.nth 63 padded 0 in
    if negb (List.forallb (Z.eqb 0) (List.firstn 31 (List.skipn 32 padded)) &&
      ((v =? 27) || (v =? 28))) then [] else
    let message_hash := Modexp.decode_be (List.firstn 32 padded) in
    let r := Modexp.decode_be (List.firstn 32 (List.skipn 64 padded)) in
    let s := Modexp.decode_be (List.firstn 32 (List.skipn 96 padded)) in
    match recover message_hash r s (v - 27) with
    | Some recovered => recovered
    | None => []
    end.

  Module Result.
    Inductive t : Set :=
    | Success (cost : Z) (output : list Z)
    | OutOfGas.
  End Result.

  Definition run (input : list Z) (gas_limit : Z) : Result.t :=
    if gas_limit <? 3000 then Result.OutOfGas
    else Result.Success 3000 (output input).
End Secp256k1.
