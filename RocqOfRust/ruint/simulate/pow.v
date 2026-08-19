Require Import simulate.RocqOfRust.
Require Import ruint.links.pow.

Module Impl_Uint.
  Definition pow {BITS LIMBS : usize} (base exp : lib.Uint.t BITS LIMBS) :
      lib.Uint.t BITS LIMBS :=
    {| lib.Uint.value := (base.(lib.Uint.value) ^ exp.(lib.Uint.value)) mod (2 ^ BITS.(Integer.value)) |}.

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
