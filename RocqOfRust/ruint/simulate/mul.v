Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import ruint.links.mul.

Module Impl_Uint.
  Definition wrapping_mul {BITS LIMBS : usize} (x1 x2 : lib.Uint.t BITS LIMBS) :
      lib.Uint.t BITS LIMBS :=
    {| lib.Uint.value := (x1.(lib.Uint.value) * x2.(lib.Uint.value)) mod (2 ^ BITS.(Integer.value)) |}.

  Lemma wrapping_mul_eq
      (stack : Stack.t)
      (BITS LIMBS : usize) (x1 x2 : lib.Uint.t BITS LIMBS) :
    {{
      SimulateM.eval_f
        (Impl_Uint.run_wrapping_mul BITS LIMBS x1 x2)
        stack 🌲
      (
        Output.Success (wrapping_mul x1 x2),
        stack
      )
    }}.
  Admitted.
End Impl_Uint.
