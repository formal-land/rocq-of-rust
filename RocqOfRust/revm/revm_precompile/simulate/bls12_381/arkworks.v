Require Import core.links.result.
Require Import revm.revm_precompile.simulate.interface.
Require Import revm.revm_precompile.simulate.modexp.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.
From Stdlib Require Import Bool List ZArith.

Import ListNotations.
Open Scope Z_scope.

(** Executable G1 and G2 specialization of bls12_381/arkworks.rs. The provider
    boundary and parsing order follow Rust. Fq uses canonical 384-bit residues,
    not Arkworks Montgomery limbs. Affine formulas model the group operation;
    correspondence with Arkworks projective arithmetic is not established. *)
Module arkworks.
  Module Fq.
    Definition MODULUS : Uint.t 384 6 :=
      {| Uint.value := 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787 |}.

    Record t : Set := { repr : Uint.t 384 6 }.

    Module Valid.
      Definition t (value : t) : Prop :=
        0 <= value.(repr).(Uint.value) < MODULUS.(Uint.value).

      Arguments t /.
    End Valid.

    Definition ZERO : t := {| repr := {| Uint.value := 0 |} |}.

    Definition ONE : t := {| repr := {| Uint.value := 1 |} |}.

    Definition FOUR : t := {| repr := {| Uint.value := 4 |} |}.

    Definition add (left right : t) : t :=
      {| repr := {| Uint.value :=
        (left.(repr).(Uint.value) + right.(repr).(Uint.value)) mod MODULUS.(Uint.value) |} |}.

    Definition sub (left right : t) : t :=
      {| repr := {| Uint.value :=
        (left.(repr).(Uint.value) - right.(repr).(Uint.value)) mod MODULUS.(Uint.value) |} |}.

    Definition mul (left right : t) : t :=
      {| repr := {| Uint.value :=
        (left.(repr).(Uint.value) * right.(repr).(Uint.value)) mod MODULUS.(Uint.value) |} |}.

    Definition square (value : t) : t := mul value value.

    Definition eq (left right : t) : bool :=
      Z.eqb left.(repr).(Uint.value) right.(repr).(Uint.value).

    Definition is_zero (value : t) : bool := eq value ZERO.

    Definition inverse (value : t) : option t :=
      if is_zero value then None else Some
        {| repr := {| Uint.value := Modexp.pow_mod value.(repr).(Uint.value)
          (MODULUS.(Uint.value) - 2) MODULUS.(Uint.value) |} |}.
  End Fq.

  Module G1Affine.
    Record t : Set := { x : Fq.t; y : Fq.t; infinity : bool }.

    Definition zero : t :=
      {| x := Fq.ZERO; y := Fq.ZERO; infinity := true |}.

    Definition is_on_curve (point : t) : bool :=
      point.(infinity) || Fq.eq (Fq.square point.(y))
        (Fq.add (Fq.mul (Fq.square point.(x)) point.(x)) Fq.FOUR).

    Module Valid.
      Definition t (point : t) : Prop :=
        Fq.Valid.t point.(x) /\ Fq.Valid.t point.(y) /\
        is_on_curve point = true /\
        (point.(infinity) = true -> point.(x) = Fq.ZERO /\ point.(y) = Fq.ZERO).

      Arguments t /.
    End Valid.
  End G1Affine.

  (** Fixed-size Rust arrays are represented by lists at this boundary.
      Reject malformed lengths/bytes as well as non-canonical field values. *)
  Definition read_fp (input_be : list u8) : Result.t Fq.t PrecompileError.t :=
    if negb (Nat.eqb (List.length input_be) 48 &&
        List.forallb (fun byte => (0 <=? byte.(Integer.value)) &&
          (byte.(Integer.value) <? 256)) input_be) then
      Result.Err PrecompileError.NonCanonicalFp
    else let value := List.fold_left
      (fun accumulator byte => 256 * accumulator + byte.(Integer.value)) input_be 0 in
      if value <? Fq.MODULUS.(Uint.value)
      then Result.Ok {| Fq.repr := {| Uint.value := value |} |}
      else Result.Err PrecompileError.NonCanonicalFp.

  Definition encode_fp (value : Fq.t) : list u8 :=
    List.map (fun index => {| Integer.value :=
      (value.(Fq.repr).(Uint.value) / 256 ^ Z.of_nat index) mod 256 |})
      (List.rev (List.seq 0 48)).

  Definition new_g1_point_no_subgroup_check (px py : Fq.t)
      : Result.t G1Affine.t PrecompileError.t :=
    if Fq.is_zero px && Fq.is_zero py then Result.Ok G1Affine.zero else
    let point := {| G1Affine.x := px; G1Affine.y := py; G1Affine.infinity := false |} in
    if G1Affine.is_on_curve point then Result.Ok point
    else Result.Err PrecompileError.Bls12381G1NotOnCurve.

  Definition read_g1_no_subgroup_check (x y : list u8)
      : Result.t G1Affine.t PrecompileError.t :=
    match read_fp x with
    | Result.Err error => Result.Err error
    | Result.Ok px =>
      match read_fp y with
      | Result.Err error => Result.Err error
      | Result.Ok py => new_g1_point_no_subgroup_check px py
      end
    end.

  Definition encode_g1_point (input : G1Affine.t) : list u8 :=
    if input.(G1Affine.infinity) then List.repeat ({| Integer.value := 0 |} : u8) 96
    else encode_fp input.(G1Affine.x) ++ encode_fp input.(G1Affine.y).

  Definition p1_add_affine (left right : G1Affine.t) : G1Affine.t :=
    if left.(G1Affine.infinity) then right else
    if right.(G1Affine.infinity) then left else
    let same_x := Fq.eq left.(G1Affine.x) right.(G1Affine.x) in
    if same_x && negb (Fq.eq left.(G1Affine.y) right.(G1Affine.y))
    then G1Affine.zero else
    let numerator := if same_x then
      let x_squared := Fq.square left.(G1Affine.x) in
      Fq.add (Fq.add x_squared x_squared) x_squared
      else Fq.sub right.(G1Affine.y) left.(G1Affine.y) in
    let denominator := if same_x then Fq.add left.(G1Affine.y) left.(G1Affine.y)
      else Fq.sub right.(G1Affine.x) left.(G1Affine.x) in
    match Fq.inverse denominator with
    | None => G1Affine.zero
    | Some inverse =>
      let slope := Fq.mul numerator inverse in
      let x := Fq.sub (Fq.sub (Fq.square slope) left.(G1Affine.x)) right.(G1Affine.x) in
      let y := Fq.sub (Fq.mul slope (Fq.sub left.(G1Affine.x) x)) left.(G1Affine.y) in
      {| G1Affine.x := x; G1Affine.y := y; G1Affine.infinity := false |}
    end.

  Definition p1_add_affine_bytes (a b : list u8 * list u8)
      : Result.t (list u8) PrecompileError.t :=
    let '(a_x, a_y) := a in
    let '(b_x, b_y) := b in
    match read_g1_no_subgroup_check a_x a_y with
    | Result.Err error => Result.Err error
    | Result.Ok p1 =>
      match read_g1_no_subgroup_check b_x b_y with
      | Result.Err error => Result.Err error
      | Result.Ok p2 => Result.Ok (encode_g1_point (p1_add_affine p1 p2))
      end
    end.

  Module Fr.
    Definition MODULUS : Uint.t 256 4 :=
      {| Uint.value := 52435875175126190479447740508185965837690552500527637822603658699938581184513 |}.

    Record t : Set := { repr : Uint.t 256 4 }.

    Module Valid.
      Definition t (value : t) : Prop :=
        0 <= value.(repr).(Uint.value) < MODULUS.(Uint.value).

      Arguments t /.
    End Valid.
  End Fr.

  (** Jacobian coordinates represent (X/Z^2, Y/Z^3). This is an executable
      group model, not a proof of Arkworks' Montgomery representation or MSM
      algorithm. Parsing establishes canonical coordinates and scalar bounds. *)
  Module G1Projective.
    Record t : Set := { x : Fq.t; y : Fq.t; z : Fq.t }.

    Definition zero : t := {| x := Fq.ZERO; y := Fq.ONE; z := Fq.ZERO |}.

    Definition is_zero (point : t) : bool := Fq.is_zero point.(z).

    Definition from_affine (point : G1Affine.t) : t :=
      if point.(G1Affine.infinity) then zero else
      {| x := point.(G1Affine.x); y := point.(G1Affine.y); z := Fq.ONE |}.

    Definition into_affine (point : t) : G1Affine.t :=
      match Fq.inverse point.(z) with
      | None => G1Affine.zero
      | Some inverse =>
        let inverse_squared := Fq.square inverse in
        {| G1Affine.x := Fq.mul point.(x) inverse_squared;
           G1Affine.y := Fq.mul point.(y) (Fq.mul inverse_squared inverse);
           G1Affine.infinity := false |}
      end.

    Definition double (point : t) : t :=
      if is_zero point || Fq.is_zero point.(y) then zero else
      let a := Fq.square point.(x) in
      let b := Fq.square point.(y) in
      let c := Fq.square b in
      let d_half := Fq.sub (Fq.sub (Fq.square (Fq.add point.(x) b)) a) c in
      let d := Fq.add d_half d_half in
      let e := Fq.add (Fq.add a a) a in
      let x := Fq.sub (Fq.square e) (Fq.add d d) in
      let c2 := Fq.add c c in
      let c4 := Fq.add c2 c2 in
      let c8 := Fq.add c4 c4 in
      let yz := Fq.mul point.(y) point.(z) in
      let y := Fq.sub (Fq.mul e (Fq.sub d x)) c8 in
      {| x := x; y := y; z := Fq.add yz yz |}.

    Definition add (left right : t) : t :=
      if is_zero left then right else
      if is_zero right then left else
      let z1z1 := Fq.square left.(z) in
      let z2z2 := Fq.square right.(z) in
      let u1 := Fq.mul left.(x) z2z2 in
      let u2 := Fq.mul right.(x) z1z1 in
      let s1 := Fq.mul left.(y) (Fq.mul right.(z) z2z2) in
      let s2 := Fq.mul right.(y) (Fq.mul left.(z) z1z1) in
      if Fq.eq u1 u2 then
        if Fq.eq s1 s2 then double left else zero
      else
        let h := Fq.sub u2 u1 in
        let h2 := Fq.add h h in
        let i := Fq.square h2 in
        let j := Fq.mul h i in
        let s_difference := Fq.sub s2 s1 in
        let r := Fq.add s_difference s_difference in
        let v := Fq.mul u1 i in
        let x := Fq.sub (Fq.sub (Fq.square r) j) (Fq.add v v) in
        let s1j := Fq.mul s1 j in
        let y := Fq.sub (Fq.mul r (Fq.sub v x)) (Fq.add s1j s1j) in
        let z := Fq.mul h
          (Fq.sub (Fq.sub (Fq.square (Fq.add left.(z) right.(z))) z1z1) z2z2) in
        {| x := x; y := y; z := z |}.

    Fixpoint mul_bits (fuel : nat) (bits : Uint.t 256 4) (point accumulator : t) : t :=
      match fuel with
      | O => accumulator
      | S fuel =>
        if Z.eqb bits.(Uint.value) 0 then accumulator else
        mul_bits fuel {| Uint.value := Z.shiftr bits.(Uint.value) 1 |}
          (double point)
          (if Z.odd bits.(Uint.value) then add accumulator point else accumulator)
      end.

    (** The integer is deliberately not reduced modulo Fr.MODULUS: subgroup
        validation must multiply by the group order itself, not by zero. *)
    Definition mul_bigint (point : G1Affine.t) (bits : Uint.t 256 4) : t :=
      mul_bits 256 bits (from_affine point) zero.
  End G1Projective.

  Definition read_g1 (x y : list u8) : Result.t G1Affine.t PrecompileError.t :=
    match read_g1_no_subgroup_check x y with
    | Result.Err error => Result.Err error
    | Result.Ok point =>
      if G1Projective.is_zero (G1Projective.mul_bigint point Fr.MODULUS)
      then Result.Ok point
      else Result.Err PrecompileError.Bls12381G1NotInSubgroup
    end.

  Definition read_scalar (input : list u8) : Result.t Fr.t PrecompileError.t :=
    if negb (Nat.eqb (List.length input) 32 &&
        List.forallb (fun byte => (0 <=? byte.(Integer.value)) &&
          (byte.(Integer.value) <? 256)) input) then
      Result.Err PrecompileError.Bls12381ScalarInputLength
    else Result.Ok {| Fr.repr := {| Uint.value :=
      (List.fold_left (fun accumulator byte =>
        256 * accumulator + byte.(Integer.value)) input 0) mod Fr.MODULUS.(Uint.value) |} |}.

  Fixpoint p1_msm_projective (points : list G1Affine.t) (scalars : list Fr.t)
      (accumulator : G1Projective.t) : option G1Projective.t :=
    match points, scalars with
    | [], [] => Some accumulator
    | point :: points, scalar :: scalars =>
      p1_msm_projective points scalars
        (G1Projective.add accumulator (G1Projective.mul_bigint point scalar.(Fr.repr)))
    | _, _ => None
    end.

  (** None represents the Rust assertion failure on unequal vector lengths.
      The byte parser constructs vectors of equal length. One inversion is
      needed only after all projective products have been accumulated. *)
  Definition p1_msm (points : list G1Affine.t) (scalars : list Fr.t)
      : option G1Affine.t :=
    option_map G1Projective.into_affine
      (p1_msm_projective points scalars G1Projective.zero).

  Fixpoint read_g1_scalar_pairs
      (pairs : list (Result.t ((list u8 * list u8) * list u8) PrecompileError.t))
      (points : list G1Affine.t) (scalars : list Fr.t)
      : Result.t (list G1Affine.t * list Fr.t) PrecompileError.t :=
    match pairs with
    | [] => Result.Ok (List.rev points, List.rev scalars)
    | Result.Err error :: _ => Result.Err error
    | Result.Ok ((x, y), scalar_bytes) :: pairs =>
      match read_g1 x y with
      | Result.Err error => Result.Err error
      | Result.Ok point =>
        if negb (Nat.eqb (List.length scalar_bytes) 32) then
          Result.Err PrecompileError.Bls12381ScalarInputLength
        else if List.forallb (fun byte => Z.eqb byte.(Integer.value) 0) scalar_bytes
        then read_g1_scalar_pairs pairs points scalars
        else match read_scalar scalar_bytes with
        | Result.Err error => Result.Err error
        | Result.Ok scalar => read_g1_scalar_pairs pairs (point :: points) (scalar :: scalars)
        end
      end
    end.

  (** The input lists model fixed-size Rust arrays. The outer precompile
      supplies exactly 32 scalar bytes; the parser also checks this length
      before the zero-scalar shortcut to enforce Rust's fixed-size boundary. None denotes the vector-length
      assertion boundary; this parser always constructs equal-length lists. *)
  Definition p1_msm_bytes
      (pairs : list (Result.t ((list u8 * list u8) * list u8) PrecompileError.t))
      : option (Result.t (list u8) PrecompileError.t) :=
    match read_g1_scalar_pairs pairs [] [] with
    | Result.Err error => Some (Result.Err error)
    | Result.Ok (points, scalars) =>
      option_map (fun point => Result.Ok (encode_g1_point point)) (p1_msm points scalars)
    end.
  (** Fq2 = Fq[i]/(i^2 + 1), with the same c0, c1 coefficient order as
      Arkworks. Each coefficient retains the canonical bounded Fq boundary. *)
  Module Fq2.
    Record t : Set := { c0 : Fq.t; c1 : Fq.t }.

    Module Valid.
      Definition t (value : t) : Prop :=
        Fq.Valid.t value.(c0) /\ Fq.Valid.t value.(c1).

      Arguments t /.
    End Valid.

    Definition ZERO : t := {| c0 := Fq.ZERO; c1 := Fq.ZERO |}.

    Definition ONE : t := {| c0 := Fq.ONE; c1 := Fq.ZERO |}.

    (** The G2 twist has coefficient b = 4 + 4i. *)
    Definition COEFF_B : t := {| c0 := Fq.FOUR; c1 := Fq.FOUR |}.

    Definition add (left right : t) : t :=
      {| c0 := Fq.add left.(c0) right.(c0);
         c1 := Fq.add left.(c1) right.(c1) |}.

    Definition sub (left right : t) : t :=
      {| c0 := Fq.sub left.(c0) right.(c0);
         c1 := Fq.sub left.(c1) right.(c1) |}.

    Definition mul (left right : t) : t :=
      {| c0 := Fq.sub (Fq.mul left.(c0) right.(c0)) (Fq.mul left.(c1) right.(c1));
         c1 := Fq.add (Fq.mul left.(c0) right.(c1)) (Fq.mul left.(c1) right.(c0)) |}.

    Definition square (value : t) : t :=
      let product := Fq.mul value.(c0) value.(c1) in
      {| c0 := Fq.mul (Fq.add value.(c0) value.(c1)) (Fq.sub value.(c0) value.(c1));
         c1 := Fq.add product product |}.

    Definition eq (left right : t) : bool :=
      Fq.eq left.(c0) right.(c0) && Fq.eq left.(c1) right.(c1).

    Definition is_zero (value : t) : bool := eq value ZERO.

    Definition inverse (value : t) : option t :=
      match Fq.inverse (Fq.add (Fq.square value.(c0)) (Fq.square value.(c1))) with
      | None => None
      | Some inverse => Some
        {| c0 := Fq.mul value.(c0) inverse;
           c1 := Fq.sub Fq.ZERO (Fq.mul value.(c1) inverse) |}
      end.
  End Fq2.

  Module G2Affine.
    Record t : Set := { x : Fq2.t; y : Fq2.t; infinity : bool }.

    Definition zero : t :=
      {| x := Fq2.ZERO; y := Fq2.ZERO; infinity := true |}.

    Definition is_on_curve (point : t) : bool :=
      point.(infinity) || Fq2.eq (Fq2.square point.(y))
        (Fq2.add (Fq2.mul (Fq2.square point.(x)) point.(x)) Fq2.COEFF_B).

    Module Valid.
      Definition t (point : t) : Prop :=
        Fq2.Valid.t point.(x) /\ Fq2.Valid.t point.(y) /\
        is_on_curve point = true /\
        (point.(infinity) = true -> point.(x) = Fq2.ZERO /\ point.(y) = Fq2.ZERO).

      Arguments t /.
    End Valid.
  End G2Affine.

  Definition read_fp2 (input_1 input_2 : list u8) : Result.t Fq2.t PrecompileError.t :=
    match read_fp input_1 with
    | Result.Err error => Result.Err error
    | Result.Ok fp_1 =>
      match read_fp input_2 with
      | Result.Err error => Result.Err error
      | Result.Ok fp_2 => Result.Ok {| Fq2.c0 := fp_1; Fq2.c1 := fp_2 |}
      end
    end.

  Definition new_g2_point_no_subgroup_check (x y : Fq2.t)
      : Result.t G2Affine.t PrecompileError.t :=
    if Fq2.is_zero x && Fq2.is_zero y then Result.Ok G2Affine.zero else
    let point := {| G2Affine.x := x; G2Affine.y := y; G2Affine.infinity := false |} in
    if G2Affine.is_on_curve point then Result.Ok point
    else Result.Err PrecompileError.Bls12381G2NotOnCurve.

  Definition read_g2_no_subgroup_check (x_0 x_1 y_0 y_1 : list u8)
      : Result.t G2Affine.t PrecompileError.t :=
    match read_fp2 x_0 x_1 with
    | Result.Err error => Result.Err error
    | Result.Ok x =>
      match read_fp2 y_0 y_1 with
      | Result.Err error => Result.Err error
      | Result.Ok y => new_g2_point_no_subgroup_check x y
      end
    end.

  Definition encode_g2_point (input : G2Affine.t) : list u8 :=
    if input.(G2Affine.infinity) then List.repeat ({| Integer.value := 0 |} : u8) 192
    else encode_fp input.(G2Affine.x).(Fq2.c0) ++ encode_fp input.(G2Affine.x).(Fq2.c1) ++
      encode_fp input.(G2Affine.y).(Fq2.c0) ++ encode_fp input.(G2Affine.y).(Fq2.c1).

  Module G2Projective.
    Record t : Set := { x : Fq2.t; y : Fq2.t; z : Fq2.t }.

    Definition zero : t := {| x := Fq2.ZERO; y := Fq2.ONE; z := Fq2.ZERO |}.

    Definition is_zero (point : t) : bool := Fq2.is_zero point.(z).

    Definition from_affine (point : G2Affine.t) : t :=
      if point.(G2Affine.infinity) then zero else
      {| x := point.(G2Affine.x); y := point.(G2Affine.y); z := Fq2.ONE |}.

    Definition into_affine (point : t) : G2Affine.t :=
      match Fq2.inverse point.(z) with
      | None => G2Affine.zero
      | Some inverse =>
        let inverse_squared := Fq2.square inverse in
        {| G2Affine.x := Fq2.mul point.(x) inverse_squared;
           G2Affine.y := Fq2.mul point.(y) (Fq2.mul inverse_squared inverse);
           G2Affine.infinity := false |}
      end.

    Definition double (point : t) : t :=
      if is_zero point || Fq2.is_zero point.(y) then zero else
      let a := Fq2.square point.(x) in
      let b := Fq2.square point.(y) in
      let c := Fq2.square b in
      let d_half := Fq2.sub (Fq2.sub (Fq2.square (Fq2.add point.(x) b)) a) c in
      let d := Fq2.add d_half d_half in
      let e := Fq2.add (Fq2.add a a) a in
      let x := Fq2.sub (Fq2.square e) (Fq2.add d d) in
      let c2 := Fq2.add c c in
      let c4 := Fq2.add c2 c2 in
      let c8 := Fq2.add c4 c4 in
      let yz := Fq2.mul point.(y) point.(z) in
      let y := Fq2.sub (Fq2.mul e (Fq2.sub d x)) c8 in
      {| x := x; y := y; z := Fq2.add yz yz |}.

    Definition add (left right : t) : t :=
      if is_zero left then right else
      if is_zero right then left else
      let z1z1 := Fq2.square left.(z) in
      let z2z2 := Fq2.square right.(z) in
      let u1 := Fq2.mul left.(x) z2z2 in
      let u2 := Fq2.mul right.(x) z1z1 in
      let s1 := Fq2.mul left.(y) (Fq2.mul right.(z) z2z2) in
      let s2 := Fq2.mul right.(y) (Fq2.mul left.(z) z1z1) in
      if Fq2.eq u1 u2 then
        if Fq2.eq s1 s2 then double left else zero
      else
        let h := Fq2.sub u2 u1 in
        let h2 := Fq2.add h h in
        let i := Fq2.square h2 in
        let j := Fq2.mul h i in
        let s_difference := Fq2.sub s2 s1 in
        let r := Fq2.add s_difference s_difference in
        let v := Fq2.mul u1 i in
        let x := Fq2.sub (Fq2.sub (Fq2.square r) j) (Fq2.add v v) in
        let s1j := Fq2.mul s1 j in
        let y := Fq2.sub (Fq2.mul r (Fq2.sub v x)) (Fq2.add s1j s1j) in
        let z := Fq2.mul h
          (Fq2.sub (Fq2.sub (Fq2.square (Fq2.add left.(z) right.(z))) z1z1) z2z2) in
        {| x := x; y := y; z := z |}.

    Fixpoint mul_bits (fuel : nat) (bits : Uint.t 256 4) (point accumulator : t) : t :=
      match fuel with
      | O => accumulator
      | S fuel =>
        if Z.eqb bits.(Uint.value) 0 then accumulator else
        mul_bits fuel {| Uint.value := Z.shiftr bits.(Uint.value) 1 |}
          (double point)
          (if Z.odd bits.(Uint.value) then add accumulator point else accumulator)
      end.

    (** The integer is deliberately not reduced modulo Fr.MODULUS: subgroup
        validation must multiply by the group order itself, not by zero. *)
    Definition mul_bigint (point : G2Affine.t) (bits : Uint.t 256 4) : t :=
      mul_bits 256 bits (from_affine point) zero.
  End G2Projective.

  (** Arkworks uses an endomorphism subgroup check. This mathematical model
      uses multiplication by the raw subgroup order; correspondence with that
      optimized check is not proved here. Preserve Rust's G1-named error. *)
  Definition read_g2 (x_0 x_1 y_0 y_1 : list u8) : Result.t G2Affine.t PrecompileError.t :=
    match read_g2_no_subgroup_check x_0 x_1 y_0 y_1 with
    | Result.Err error => Result.Err error
    | Result.Ok point =>
      if G2Projective.is_zero (G2Projective.mul_bigint point Fr.MODULUS)
      then Result.Ok point
      else Result.Err PrecompileError.Bls12381G1NotInSubgroup
    end.

  Definition p2_add_affine (left right : G2Affine.t) : G2Affine.t :=
    G2Projective.into_affine
      (G2Projective.add (G2Projective.from_affine left) (G2Projective.from_affine right)).

  Definition p2_add_affine_bytes (a b : list u8 * list u8 * list u8 * list u8)
      : Result.t (list u8) PrecompileError.t :=
    let '(a_x_0, a_x_1, a_y_0, a_y_1) := a in
    let '(b_x_0, b_x_1, b_y_0, b_y_1) := b in
    match read_g2_no_subgroup_check a_x_0 a_x_1 a_y_0 a_y_1 with
    | Result.Err error => Result.Err error
    | Result.Ok p1 =>
      match read_g2_no_subgroup_check b_x_0 b_x_1 b_y_0 b_y_1 with
      | Result.Err error => Result.Err error
      | Result.Ok p2 => Result.Ok (encode_g2_point (p2_add_affine p1 p2))
      end
    end.

  Fixpoint p2_msm_projective (points : list G2Affine.t) (scalars : list Fr.t)
      (accumulator : G2Projective.t) : option G2Projective.t :=
    match points, scalars with
    | [], [] => Some accumulator
    | point :: points, scalar :: scalars =>
      p2_msm_projective points scalars
        (G2Projective.add accumulator (G2Projective.mul_bigint point scalar.(Fr.repr)))
    | _, _ => None
    end.

  (** None represents the Rust assertion failure on unequal vector lengths.
      The byte parser constructs vectors of equal length. One inversion is
      needed only after all projective products have been accumulated. *)
  Definition p2_msm (points : list G2Affine.t) (scalars : list Fr.t)
      : option G2Affine.t :=
    option_map G2Projective.into_affine
      (p2_msm_projective points scalars G2Projective.zero).

  Fixpoint read_g2_scalar_pairs
      (pairs : list (Result.t ((list u8 * list u8 * list u8 * list u8) * list u8) PrecompileError.t))
      (points : list G2Affine.t) (scalars : list Fr.t)
      : Result.t (list G2Affine.t * list Fr.t) PrecompileError.t :=
    match pairs with
    | [] => Result.Ok (List.rev points, List.rev scalars)
    | Result.Err error :: _ => Result.Err error
    | Result.Ok ((x_0, x_1, y_0, y_1), scalar_bytes) :: pairs =>
      match read_g2 x_0 x_1 y_0 y_1 with
      | Result.Err error => Result.Err error
      | Result.Ok point =>
        if negb (Nat.eqb (List.length scalar_bytes) 32) then
          Result.Err PrecompileError.Bls12381ScalarInputLength
        else if List.forallb (fun byte => Z.eqb byte.(Integer.value) 0) scalar_bytes
        then read_g2_scalar_pairs pairs points scalars
        else match read_scalar scalar_bytes with
        | Result.Err error => Result.Err error
        | Result.Ok scalar => read_g2_scalar_pairs pairs (point :: points) (scalar :: scalars)
        end
      end
    end.

  (** The input lists model fixed-size Rust arrays. The outer precompile
      supplies exactly 32 scalar bytes; the parser also checks this length
      before the zero-scalar shortcut to enforce Rust's fixed-size boundary. None denotes the vector-length
      assertion boundary; this parser always constructs equal-length lists. *)
  Definition p2_msm_bytes
      (pairs : list (Result.t ((list u8 * list u8 * list u8 * list u8) * list u8) PrecompileError.t))
      : option (Result.t (list u8) PrecompileError.t) :=
    match read_g2_scalar_pairs pairs [] [] with
    | Result.Err error => Some (Result.Err error)
    | Result.Ok (points, scalars) =>
      option_map (fun point => Result.Ok (encode_g2_point point)) (p2_msm points scalars)
    end.
End arkworks.
