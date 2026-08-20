Require Import simulate.RocqOfRust.
Require Import ruint.links.pow.

Module Impl_Uint.
  Fixpoint pow_mod_positive
      (base : Z) (exponent : positive) (modulus : Z) : Z :=
    match exponent with
    | xH => base mod modulus
    | xO exponent =>
        let result := pow_mod_positive base exponent modulus in
        (result * result) mod modulus
    | xI exponent =>
        let result := pow_mod_positive base exponent modulus in
        let square := (result * result) mod modulus in
        (base * square) mod modulus
    end.

  Definition pow_mod (base exponent modulus : Z) : Z :=
    match exponent with
    | Z0 => 1 mod modulus
    | Zpos exponent => pow_mod_positive base exponent modulus
    | Zneg _ => 0
    end.

  Definition pow {BITS LIMBS : usize} (base exp : lib.Uint.t BITS LIMBS) :
      lib.Uint.t BITS LIMBS :=
    let modulus := 2 ^ BITS.(Integer.value) in
    {| lib.Uint.value :=
        pow_mod base.(lib.Uint.value) exp.(lib.Uint.value) modulus |}.

  Lemma pow_eq
      (stack : Stack.t)
      (BITS LIMBS : usize) (base exp : lib.Uint.t BITS LIMBS) :
    {{
      SimulateM.eval_f
        (Impl_Uint.run_pow BITS LIMBS base exp)
        stack 🌲
      (
        Output.Success (pow base exp),
        stack
      )
    }}.
  Proof.
  Admitted.
End Impl_Uint.
