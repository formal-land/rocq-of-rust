Require Import revm.revm_precompile.simulate.bls12_381.arkworks.
Require Import revm.revm_precompile.simulate.modexp.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.
From Stdlib Require Import Bool List ZArith.

Import ListNotations arkworks.
Open Scope Z_scope.

(** Mathematical specialization of ark-bls12-381 g2_swu_iso.rs and the
    ark-ec SWU/WB maps. Canonical residues replace Montgomery arithmetic.
    Square roots are checked explicitly; correspondence with Arkworks field
    square-root internals is not proved here. *)
Module g2_swu_iso.
  Definition fq_sqrt (value : Fq.t) : option Fq.t :=
    let root := {| Fq.repr := {| Uint.value :=
      Modexp.pow_mod value.(Fq.repr).(Uint.value)
        ((Fq.MODULUS.(Uint.value) + 1) / 4) Fq.MODULUS.(Uint.value) |} |} in
    if Fq.eq (Fq.square root) value then Some root else None.

  Definition TWO_INV : Fq.t :=
    {| Fq.repr := {| Uint.value := (Fq.MODULUS.(Uint.value) + 1) / 2 |} |}.

  Definition fq2_sqrt_candidate (value : Fq2.t) (norm_root : Fq.t) : option Fq2.t :=
    match fq_sqrt (Fq.mul (Fq.add value.(Fq2.c0) norm_root) TWO_INV) with
    | None => None
    | Some real =>
      match Fq.inverse (Fq.add real real) with
      | None => None
      | Some inv =>
        let root := {| Fq2.c0 := real; Fq2.c1 := Fq.mul value.(Fq2.c1) inv |} in
        if Fq2.eq (Fq2.square root) value then Some root else None
      end
    end.

  Definition fq2_sqrt (value : Fq2.t) : option Fq2.t :=
    if Fq.is_zero value.(Fq2.c1) then
      match fq_sqrt value.(Fq2.c0) with
      | Some root => Some {| Fq2.c0 := root; Fq2.c1 := Fq.ZERO |}
      | None =>
        match fq_sqrt (Fq.sub Fq.ZERO value.(Fq2.c0)) with
        | Some root => Some {| Fq2.c0 := Fq.ZERO; Fq2.c1 := root |}
        | None => None
        end
      end
    else
      match fq_sqrt (Fq.add (Fq.square value.(Fq2.c0)) (Fq.square value.(Fq2.c1))) with
      | None => None
      | Some norm_root =>
        match fq2_sqrt_candidate value norm_root with
        | Some root => Some root
        | None => fq2_sqrt_candidate value (Fq.sub Fq.ZERO norm_root)
        end
      end.

  Definition parity (value : Fq2.t) : bool :=
    Z.odd (if Fq.is_zero value.(Fq2.c0)
      then value.(Fq2.c1).(Fq.repr).(Uint.value)
      else value.(Fq2.c0).(Fq.repr).(Uint.value)).

  Definition COEFF_A : Fq2.t :=
    {| Fq2.c0 := Fq.ZERO; Fq2.c1 := {| Fq.repr := {| Uint.value := 240 |} |} |}.

  Definition COEFF_B : Fq2.t :=
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 1012 |} |};
       Fq2.c1 := {| Fq.repr := {| Uint.value := 1012 |} |} |}.

  Definition ZETA : Fq2.t :=
    {| Fq2.c0 := Fq.sub Fq.ZERO (Fq.add Fq.ONE Fq.ONE);
       Fq2.c1 := Fq.sub Fq.ZERO Fq.ONE |}.

  Definition map_to_curve (element : Fq2.t) : option (Fq2.t * Fq2.t) :=
    let zeta_u2 := Fq2.mul ZETA (Fq2.square element) in
    let ta := Fq2.add (Fq2.square zeta_u2) zeta_u2 in
    let num_x1 := Fq2.mul COEFF_B (Fq2.add ta Fq2.ONE) in
    let div := Fq2.mul COEFF_A
      (if Fq2.is_zero ta then ZETA else Fq2.sub Fq2.ZERO ta) in
    match Fq2.inverse div with
    | None => None
    | Some div_inv =>
      let x1 := Fq2.mul num_x1 div_inv in
      let gx1 := Fq2.add (Fq2.mul (Fq2.add (Fq2.square x1) COEFF_A) x1) COEFF_B in
      let candidate :=
        match (if Fq2.is_zero gx1 then None else fq2_sqrt gx1) with
        | Some y1 => Some (x1, y1)
        | None =>
          match fq2_sqrt (Fq2.mul ZETA gx1) with
          | None => None
          | Some y1 => Some (Fq2.mul zeta_u2 x1,
              Fq2.mul (Fq2.mul zeta_u2 element) y1)
          end
        end in
      match candidate with
      | None => None
      | Some (x, y) => Some (x,
          if Bool.eqb (parity y) (parity element) then y else Fq2.sub Fq2.ZERO y)
      end
    end.

  Definition x_map_numerator : list Fq2.t := [
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235542 |} |};
       Fq2.c1 := {| Fq.repr := {| Uint.value := 889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235542 |} |} |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 0 |} |};
       Fq2.c1 := {| Fq.repr := {| Uint.value := 2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706522 |} |} |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706526 |} |};
       Fq2.c1 := {| Fq.repr := {| Uint.value := 1334136518407222464472596608578634718852294273313002628444019378708010550163612621480895876376338554679298090853261 |} |} |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 3557697382419259905260257622876359250272784728834673675850718343221361467102966990615722337003569479144794908942033 |} |};
       Fq2.c1 := {| Fq.repr := {| Uint.value := 0 |} |} |}
  ].

  Definition x_map_denominator : list Fq2.t := [
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 0 |} |};
       Fq2.c1 := {| Fq.repr := {| Uint.value := 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559715 |} |} |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 12 |} |};
       Fq2.c1 := {| Fq.repr := {| Uint.value := 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559775 |} |} |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 1 |} |};
       Fq2.c1 := {| Fq.repr := {| Uint.value := 0 |} |} |}
  ].

  Definition y_map_numerator : list Fq2.t := [
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 3261222600550988246488569487636662646083386001431784202863158481286248011511053074731078808919938689216061999863558 |} |};
       Fq2.c1 := {| Fq.repr := {| Uint.value := 3261222600550988246488569487636662646083386001431784202863158481286248011511053074731078808919938689216061999863558 |} |} |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 0 |} |};
       Fq2.c1 := {| Fq.repr := {| Uint.value := 889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235518 |} |} |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706524 |} |};
       Fq2.c1 := {| Fq.repr := {| Uint.value := 1334136518407222464472596608578634718852294273313002628444019378708010550163612621480895876376338554679298090853263 |} |} |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 2816510427748580758331037284777117739799287910327449993381818688383577828123182200904113516794492504322962636245776 |} |};
       Fq2.c1 := {| Fq.repr := {| Uint.value := 0 |} |} |}
  ].

  Definition y_map_denominator : list Fq2.t := [
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559355 |} |};
       Fq2.c1 := {| Fq.repr := {| Uint.value := 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559355 |} |} |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 0 |} |};
       Fq2.c1 := {| Fq.repr := {| Uint.value := 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559571 |} |} |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 18 |} |};
       Fq2.c1 := {| Fq.repr := {| Uint.value := 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559769 |} |} |};
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 1 |} |};
       Fq2.c1 := {| Fq.repr := {| Uint.value := 0 |} |} |}
  ].

  Fixpoint evaluate (coefficients : list Fq2.t) (x : Fq2.t) : Fq2.t :=
    match coefficients with
    | [] => Fq2.ZERO
    | coefficient :: rest => Fq2.add coefficient (Fq2.mul x (evaluate rest x))
    end.

  (** Arkworks batch inversion leaves zero entries zero. *)
  Definition inverse_or_zero (value : Fq2.t) : Fq2.t :=
    match Fq2.inverse value with Some inv => inv | None => Fq2.ZERO end.

  Definition apply_isogeny (point : Fq2.t * Fq2.t) : G2Affine.t :=
    let '(x, y) := point in
    {| G2Affine.x := Fq2.mul (evaluate x_map_numerator x)
         (inverse_or_zero (evaluate x_map_denominator x));
       G2Affine.y := Fq2.mul (Fq2.mul (evaluate y_map_numerator x) y)
         (inverse_or_zero (evaluate y_map_denominator x));
       G2Affine.infinity := false |}.

  Definition P_POWER_ENDOMORPHISM_COEFF_0 : Fq2.t :=
    {| Fq2.c0 := Fq.ZERO;
       Fq2.c1 := {| Fq.repr := {| Uint.value := 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437 |} |} |}.

  Definition P_POWER_ENDOMORPHISM_COEFF_1 : Fq2.t :=
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530 |} |};
       Fq2.c1 := {| Fq.repr := {| Uint.value := 1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257 |} |} |}.

  Definition DOUBLE_P_POWER_ENDOMORPHISM_COEFF_0 : Fq2.t :=
    {| Fq2.c0 := {| Fq.repr := {| Uint.value := 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436 |} |};
       Fq2.c1 := Fq.ZERO |}.

  Definition conjugate (value : Fq2.t) : Fq2.t :=
    {| Fq2.c0 := value.(Fq2.c0); Fq2.c1 := Fq.sub Fq.ZERO value.(Fq2.c1) |}.

  Definition p_power_endomorphism (point : G2Affine.t) : G2Affine.t :=
    {| G2Affine.x := Fq2.mul (conjugate point.(G2Affine.x)) P_POWER_ENDOMORPHISM_COEFF_0;
       G2Affine.y := Fq2.mul (conjugate point.(G2Affine.y)) P_POWER_ENDOMORPHISM_COEFF_1;
       G2Affine.infinity := point.(G2Affine.infinity) |}.

  Definition double_p_power_endomorphism (point : G2Projective.t) : G2Projective.t :=
    {| G2Projective.x := Fq2.mul point.(G2Projective.x) DOUBLE_P_POWER_ENDOMORPHISM_COEFF_0;
       G2Projective.y := Fq2.sub Fq2.ZERO point.(G2Projective.y);
       G2Projective.z := point.(G2Projective.z) |}.

  Definition neg (point : G2Projective.t) : G2Projective.t :=
    {| G2Projective.x := point.(G2Projective.x);
       G2Projective.y := Fq2.sub Fq2.ZERO point.(G2Projective.y);
       G2Projective.z := point.(G2Projective.z) |}.

  Definition X_ABS : Uint.t 256 4 := {| Uint.value := 15132376222941642752 |}.

  Definition clear_cofactor (point : G2Affine.t) : G2Affine.t :=
    let p_projective := G2Projective.from_affine point in
    let x_p := neg (G2Projective.mul_bigint point X_ABS) in
    let psi_p := G2Projective.from_affine (p_power_endomorphism point) in
    let psi2_p2 := double_p_power_endomorphism (G2Projective.double p_projective) in
    let tmp := G2Projective.add x_p psi_p in
    let tmp2 := neg (G2Projective.mul_bits 256 X_ABS tmp G2Projective.zero) in
    G2Projective.into_affine (G2Projective.add
      (G2Projective.add (G2Projective.add (G2Projective.add psi2_p2 tmp2) (neg x_p))
        (neg psi_p)) (neg p_projective)).

  Definition map_fp2_to_g2 (element : Fq2.t) : option G2Affine.t :=
    match map_to_curve element with
    | None => None
    | Some point => Some (clear_cofactor (apply_isogeny point))
    end.
End g2_swu_iso.
