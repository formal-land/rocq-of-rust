Require Import simulate.RocqOfRust.
Require Import ruint.links.div.

Module Impl_Uint.
  Definition wrapping_div {BITS LIMBS : usize} (x1 x2 : lib.Uint.t BITS LIMBS) :
      lib.Uint.t BITS LIMBS :=
    {| lib.Uint.value := x1.(lib.Uint.value) / x2.(lib.Uint.value) |}.

  Lemma wrapping_div_eq
      (stack : Stack.t)
      (BITS LIMBS : usize) (x1 x2 : lib.Uint.t BITS LIMBS) :
    {{
      SimulateM.eval_f
        (Impl_Uint.run_wrapping_div BITS LIMBS x1 x2)
        stack 🌲
      (
        Output.Success (wrapping_div x1 x2),
        stack
      )
    }}.
  Admitted.
  Definition wrapping_rem {BITS LIMBS : usize} (x1 x2 : lib.Uint.t BITS LIMBS) :
      lib.Uint.t BITS LIMBS :=
    {| lib.Uint.value := x1.(lib.Uint.value) mod x2.(lib.Uint.value) |}.

  Lemma wrapping_rem_eq
      (stack : Stack.t)
      (BITS LIMBS : usize) (x1 x2 : lib.Uint.t BITS LIMBS) :
    {{
      SimulateM.eval_f
        (Impl_Uint.run_wrapping_rem BITS LIMBS x1 x2)
        stack 🌲
      (
        Output.Success (wrapping_rem x1 x2),
        stack
      )
    }}.
  Admitted.
End Impl_Uint.
