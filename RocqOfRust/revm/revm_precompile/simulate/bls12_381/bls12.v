Require Import revm.revm_precompile.simulate.bls12_381.arkworks.
Require Import revm.revm_precompile.simulate.bls12_381.fq12.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.
From Stdlib Require Import Bool List ZArith.

Import ListNotations arkworks.
Open Scope Z_scope.

(** BLS12-381 specialization of ark-ec 0.5 models/bls12/{g2,mod}.rs.
    Homogeneous line formulas, the M twist, signed family parameter and final
    exponentiation follow Rust. Field operations use canonical residues; no
    correspondence theorem with Arkworks limb arithmetic is claimed. *)
Module Bls12.
  Definition X : u64 := {| Integer.value := 15132376222941642752 |}.

  Definition X_IS_NEGATIVE : bool := true.

  Definition loop_bits : list bool :=
    List.map (fun index =>
      let bit : usize := {| Integer.value := Z.of_nat index |} in
      Z.testbit X.(Integer.value) bit.(Integer.value)) (List.rev (List.seq 0 63)).

  Definition mul_by_fp (value : Fq2.t) (scalar : Fq.t) : Fq2.t :=
    {| Fq2.c0 := Fq.mul value.(Fq2.c0) scalar;
       Fq2.c1 := Fq.mul value.(Fq2.c1) scalar |}.

  Definition triple (value : Fq2.t) : Fq2.t := Fq2.add (Fq2.add value value) value.

  Definition EllCoeff : Set := Fq2.t * Fq2.t * Fq2.t.

  Module G2HomProjective.
    Record t : Set := { x : Fq2.t; y : Fq2.t; z : Fq2.t }.

    Definition double_in_place (state : t) (two_inv : Fq.t) : t * EllCoeff :=
      let a := mul_by_fp (Fq2.mul state.(x) state.(y)) two_inv in
      let b := Fq2.square state.(y) in
      let c := Fq2.square state.(z) in
      let e := Fq2.mul Fq2.COEFF_B (triple c) in
      let f := triple e in
      let g := mul_by_fp (Fq2.add b f) two_inv in
      let h := Fq2.sub (Fq2.square (Fq2.add state.(y) state.(z))) (Fq2.add b c) in
      let i := Fq2.sub e b in
      let j := Fq2.square state.(x) in
      ({| x := Fq2.mul a (Fq2.sub b f);
          y := Fq2.sub (Fq2.square g) (triple (Fq2.square e));
          z := Fq2.mul b h |}, (i, triple j, Fq2.sub Fq2.ZERO h)).

    Definition add_in_place (state : t) (q : G2Affine.t) : t * EllCoeff :=
      let theta := Fq2.sub state.(y) (Fq2.mul q.(G2Affine.y) state.(z)) in
      let lambda := Fq2.sub state.(x) (Fq2.mul q.(G2Affine.x) state.(z)) in
      let c := Fq2.square theta in
      let d := Fq2.square lambda in
      let e := Fq2.mul lambda d in
      let f := Fq2.mul state.(z) c in
      let g := Fq2.mul state.(x) d in
      let h := Fq2.sub (Fq2.add e f) (Fq2.add g g) in
      let j := Fq2.sub (Fq2.mul theta q.(G2Affine.x)) (Fq2.mul lambda q.(G2Affine.y)) in
      ({| x := Fq2.mul lambda h;
          y := Fq2.sub (Fq2.mul theta (Fq2.sub g h)) (Fq2.mul e state.(y));
          z := Fq2.mul state.(z) e |}, (j, Fq2.sub Fq2.ZERO theta, lambda)).
  End G2HomProjective.

  Module G2Prepared.
    Record t : Set := { ell_coeffs : list EllCoeff; infinity : bool }.

    Fixpoint prepare_bits (bits : list bool) (q : G2Affine.t)
        (state : G2HomProjective.t) (two_inv : Fq.t) : list EllCoeff :=
      match bits with
      | [] => []
      | bit :: rest =>
        let '(doubled, double_coeff) := G2HomProjective.double_in_place state two_inv in
        if bit then
          let '(added, add_coeff) := G2HomProjective.add_in_place doubled q in
          double_coeff :: add_coeff :: prepare_bits rest q added two_inv
        else double_coeff :: prepare_bits rest q doubled two_inv
      end.

    Definition from (q : G2Affine.t) : t :=
      if q.(G2Affine.infinity) then {| ell_coeffs := []; infinity := true |} else
      let two_inv : Fq.t := {| Fq.repr := {| Uint.value :=
        (Fq.MODULUS.(Uint.value) + 1) / 2 |} |} in
      {| ell_coeffs := prepare_bits loop_bits q
          {| G2HomProjective.x := q.(G2Affine.x);
             G2HomProjective.y := q.(G2Affine.y);
             G2HomProjective.z := Fq2.ONE |} two_inv;
         infinity := false |}.
  End G2Prepared.

  Definition ell (f : Fq12.t) (coeffs : EllCoeff) (p : G1Affine.t) : Fq12.t :=
    let '(c0, c1, c2) := coeffs in
    Fq12.mul_by_014 f c0 (mul_by_fp c1 p.(G1Affine.x)) (mul_by_fp c2 p.(G1Affine.y)).

  Definition PreparedPair : Set := G1Affine.t * list EllCoeff.

  Fixpoint evaluate_lines (pairs : list PreparedPair) (f : Fq12.t)
      : option (list PreparedPair * Fq12.t) :=
    match pairs with
    | [] => Some ([], f)
    | (p, coeffs) :: rest =>
      match coeffs with
      | [] => None
      | coefficient :: remaining =>
        match evaluate_lines rest (ell f coefficient p) with
        | None => None
        | Some (updated, result) => Some ((p, remaining) :: updated, result)
        end
      end
    end.

  Fixpoint miller_bits (bits : list bool) (pairs : list PreparedPair) (f : Fq12.t)
      : option Fq12.t :=
    match bits with
    | [] => Some f
    | bit :: rest =>
      match evaluate_lines pairs (Fq12.square f) with
      | None => None
      | Some (pairs, f) =>
        if bit then
          match evaluate_lines pairs f with
          | None => None
          | Some (pairs, f) => miller_bits rest pairs f
          end
        else miller_bits rest pairs f
      end
    end.

  Definition multi_miller_loop (pairs : list (G1Affine.t * G2Affine.t)) : option Fq12.t :=
    let prepared := List.map (fun '(p, q) => (p, (G2Prepared.from q).(G2Prepared.ell_coeffs)))
      (List.filter (fun '(p, q) => negb (p.(G1Affine.infinity) || q.(G2Affine.infinity))) pairs) in
    match prepared with
    | [] => Some Fq12.ONE
    | _ =>
      match miller_bits loop_bits prepared Fq12.ONE with
      | None => None
      | Some f => Some (if X_IS_NEGATIVE then Fq12.conjugate f else f)
      end
    end.

  (** Structural fuel is the width of Rust's single u64 family parameter.
      Generic field squaring equals cyclotomic squaring on these inputs. *)
  Fixpoint exp_bits (fuel : nat) (bits : u64) (base accumulator : Fq12.t) : Fq12.t :=
    match fuel with
    | O => accumulator
    | S remaining =>
      let accumulator := if Z.odd bits.(Integer.value)
        then Fq12.mul accumulator base else accumulator in
      exp_bits remaining {| Integer.value := Z.shiftr bits.(Integer.value) 1 |}
        (Fq12.square base) accumulator
    end.

  Definition exp_by_x (f : Fq12.t) : Fq12.t :=
    let result := exp_bits 64 X f Fq12.ONE in
    if X_IS_NEGATIVE then Fq12.conjugate result else result.

  Definition final_exponentiation (f : Fq12.t) : option Fq12.t :=
    let f1 := Fq12.conjugate f in
    match Fq12.inverse f with
    | None => None
    | Some f2 =>
      let r := Fq12.mul f1 f2 in
      let f2 := r in
      let r := Fq12.mul (Fq12.frobenius_map r {| Integer.value := 2 |}) f2 in
      let y0 := Fq12.square r in
      let y1 := exp_by_x r in
      let y2 := Fq12.conjugate r in
      let y1 := Fq12.mul y1 y2 in
      let y2 := exp_by_x y1 in
      let y1 := Fq12.mul (Fq12.conjugate y1) y2 in
      let y2 := exp_by_x y1 in
      let y1 := Fq12.mul (Fq12.frobenius_map y1 {| Integer.value := 1 |}) y2 in
      let r := Fq12.mul r y0 in
      let y0 := exp_by_x y1 in
      let y2 := exp_by_x y0 in
      let y0 := Fq12.frobenius_map y1 {| Integer.value := 2 |} in
      let y1 := Fq12.mul (Fq12.mul (Fq12.conjugate y1) y2) y0 in
      Some (Fq12.mul r y1)
    end.

  Definition pairing_check (pairs : list (G1Affine.t * G2Affine.t)) : option bool :=
    match multi_miller_loop pairs with
    | None => None
    | Some f =>
      match final_exponentiation f with
      | None => None
      | Some result => Some (Fq12.eq result Fq12.ONE)
      end
    end.
End Bls12.
