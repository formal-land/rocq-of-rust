Require Import core.links.result.
Require Import revm.revm_precompile.simulate.bls12_381.arkworks.
Require Import revm.revm_precompile.simulate.bls12_381.bls12.
Require Import revm.revm_precompile.simulate.bls12_381.g1_swu_iso.
Require Import revm.revm_precompile.simulate.interface.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.
From Stdlib Require Import Bool List ZArith.

Import ListNotations arkworks.
Open Scope Z_scope.

(** Executable specialization of kzg_point_evaluation/arkworks.rs. The group
    equation and checked parsers follow Rust, using canonical field residues.
    This does not prove correspondence with Arkworks Montgomery arithmetic. *)
Module arkworks.
  Definition parse_g1_compressed (bytes : list u8)
      : Result.t G1Affine.t PrecompileError.t :=
    if negb (Nat.eqb (List.length bytes) 48 &&
        List.forallb (fun byte => (0 <=? byte.(Integer.value)) &&
          (byte.(Integer.value) <? 256)) bytes)
    then Result.Err PrecompileError.KzgInvalidG1Point else
    match bytes with
    | [] => Result.Err PrecompileError.KzgInvalidG1Point
    | first :: rest =>
      let compressed := Z.testbit first.(Integer.value) 7 in
      let infinity := Z.testbit first.(Integer.value) 6 in
      let largest := Z.testbit first.(Integer.value) 5 in
      let x_bytes := ({| Integer.value := Z.land first.(Integer.value) 31 |} : u8) :: rest in
      if negb compressed || (infinity && largest)
      then Result.Err PrecompileError.KzgInvalidG1Point else
      if infinity then
        if List.forallb (fun byte => Z.eqb byte.(Integer.value) 0) x_bytes
        then Result.Ok G1Affine.zero
        else Result.Err PrecompileError.KzgInvalidG1Point
      else match read_fp x_bytes with
      | Result.Err _ => Result.Err PrecompileError.KzgInvalidG1Point
      | Result.Ok x =>
        let rhs := Fq.add (Fq.mul (Fq.square x) x) Fq.FOUR in
        match g1_swu_iso.sqrt rhs with
        | None => Result.Err PrecompileError.KzgInvalidG1Point
        | Some root =>
          let neg_root := Fq.sub Fq.ZERO root in
          let root_is_largest := Z.ltb neg_root.(Fq.repr).(Uint.value)
            root.(Fq.repr).(Uint.value) in
          let y := if Bool.eqb largest root_is_largest then root else neg_root in
          let point := {| G1Affine.x := x; G1Affine.y := y; G1Affine.infinity := false |} in
          if G1Projective.is_zero (G1Projective.mul_bigint point Fr.MODULUS)
          then Result.Ok point else Result.Err PrecompileError.KzgInvalidG1Point
        end
      end
    end.

  Definition read_scalar_canonical (bytes : list u8)
      : Result.t Fr.t PrecompileError.t :=
    if negb (Nat.eqb (List.length bytes) 32 &&
        List.forallb (fun byte => (0 <=? byte.(Integer.value)) &&
          (byte.(Integer.value) <? 256)) bytes)
    then Result.Err PrecompileError.NonCanonicalFp else
    let value := List.fold_left
      (fun accumulator byte => 256 * accumulator + byte.(Integer.value)) bytes 0 in
    if value <? Fr.MODULUS.(Uint.value)
    then Result.Ok {| Fr.repr := {| Uint.value := value |} |}
    else Result.Err PrecompileError.NonCanonicalFp.

  (** Coordinates obtained by deserializing TRUSTED_SETUP_TAU_G2_BYTES from
      bls12_381_const.rs, pinned to consensus-specs commit
      adc514a1c29532ebc1a67c71dc8741a2fdac5ed4,
      presets/mainnet/trusted_setups/trusted_setup_4096.json, g2_monomial_1.
      The compressed representation stores x.c1 before
      x.c0 and selects the lexicographically larger y (c1 before c0). *)
  Definition get_trusted_setup_g2 : G2Affine.t :=
    {| G2Affine.x :=
        {| Fq2.c0 := {| Fq.repr := {| Uint.value := 3749701713850085193403383609513386037494151572263731328608276629425322978272408394373143740944003571525027436289778 |} |};
           Fq2.c1 := {| Fq.repr := {| Uint.value := 3347537128081568434923729147580015899756771550835613107520576615563260658656019591232316627827007503930666726825842 |} |} |};
       G2Affine.y :=
        {| Fq2.c0 := {| Fq.repr := {| Uint.value := 194392958648403190675529552496435226424111592982833162118538452666741235889530674000225873281133418439621742897817 |} |};
           Fq2.c1 := {| Fq.repr := {| Uint.value := 3447898402727835650716129438012169492682148398295533958400255525306573911008434577489634554212211450783070687991119 |} |} |};
       G2Affine.infinity := false |}.

  Definition get_g1_generator : G1Affine.t :=
    {| G1Affine.x := {| Fq.repr := {| Uint.value := 3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507 |} |};
       G1Affine.y := {| Fq.repr := {| Uint.value := 1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569 |} |};
       G1Affine.infinity := false |}.

  Definition get_g2_generator : G2Affine.t :=
    {| G2Affine.x :=
        {| Fq2.c0 := {| Fq.repr := {| Uint.value := 352701069587466618187139116011060144890029952792775240219908644239793785735715026873347600343865175952761926303160 |} |};
           Fq2.c1 := {| Fq.repr := {| Uint.value := 3059144344244213709971259814753781636986470325476647558659373206291635324768958432433509563104347017837885763365758 |} |} |};
       G2Affine.y :=
        {| Fq2.c0 := {| Fq.repr := {| Uint.value := 1985150602287291935568054521177171638300868978215655730859378665066344726373823718423869104263333984641494340347905 |} |};
           Fq2.c1 := {| Fq.repr := {| Uint.value := 927553665492332455747201965776037880757740193453592970025027978793976877002675564980949289727957565575433344219582 |} |} |};
       G2Affine.infinity := false |}.

  Definition p1_scalar_mul (point : G1Affine.t) (scalar : Fr.t) : G1Affine.t :=
    G1Projective.into_affine (G1Projective.mul_bigint point scalar.(Fr.repr)).

  Definition p2_scalar_mul (point : G2Affine.t) (scalar : Fr.t) : G2Affine.t :=
    G2Projective.into_affine (G2Projective.mul_bigint point scalar.(Fr.repr)).

  Definition p1_sub_affine (a b : G1Affine.t) : G1Affine.t :=
    let neg_b := {| G1Affine.x := b.(G1Affine.x);
      G1Affine.y := Fq.sub Fq.ZERO b.(G1Affine.y);
      G1Affine.infinity := b.(G1Affine.infinity) |} in
    G1Projective.into_affine
      (G1Projective.add (G1Projective.from_affine a) (G1Projective.from_affine neg_b)).

  Definition p2_neg (point : G2Affine.t) : G2Affine.t :=
    {| G2Affine.x := point.(G2Affine.x);
       G2Affine.y := Fq2.sub Fq2.ZERO point.(G2Affine.y);
       G2Affine.infinity := point.(G2Affine.infinity) |}.

  Definition p2_sub_affine (a b : G2Affine.t) : G2Affine.t :=
    G2Projective.into_affine
      (G2Projective.add (G2Projective.from_affine a) (G2Projective.from_affine (p2_neg b))).

  (** None preserves unexpected internal pairing failures as incomplete
      execution. Invalid encodings, scalars and proofs return Some false. *)
  Definition verify_kzg_proof (commitment z y proof : list u8) : option bool :=
    match parse_g1_compressed commitment with
    | Result.Err _ => Some false
    | Result.Ok commitment_point =>
      match parse_g1_compressed proof with
      | Result.Err _ => Some false
      | Result.Ok proof_point =>
        match read_scalar_canonical z with
        | Result.Err _ => Some false
        | Result.Ok z_fr =>
          match read_scalar_canonical y with
          | Result.Err _ => Some false
          | Result.Ok y_fr =>
            let g1 := get_g1_generator in
            let g2 := get_g2_generator in
            let p_minus_y := p1_sub_affine commitment_point (p1_scalar_mul g1 y_fr) in
            if p_minus_y.(G1Affine.infinity) && proof_point.(G1Affine.infinity)
            then Some true
            else
              let x_minus_z := p2_sub_affine get_trusted_setup_g2 (p2_scalar_mul g2 z_fr) in
              Bls12.pairing_check [(p_minus_y, p2_neg g2); (proof_point, x_minus_z)]
          end
        end
      end
    end.
End arkworks.
