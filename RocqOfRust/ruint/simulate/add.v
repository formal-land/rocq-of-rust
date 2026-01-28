Require Import links.RocqOfRust.
Require Import RocqOfRust.simulate.M.
Require Import ruint.links.add.

Module Impl_Uint.
  Definition wrapping_add {BITS LIMBS : usize} (x1 x2 : lib.Uint.t BITS LIMBS) :
      lib.Uint.t BITS LIMBS :=
    {| lib.Uint.value := (x1.(lib.Uint.value) + x2.(lib.Uint.value)) mod (2 ^ BITS.(Integer.value)) |}.

  Lemma wrapping_add_eq (stack : Stack.t)
      (BITS LIMBS : usize) (x1 x2 : lib.Uint.t BITS LIMBS) :
    {{
      SimulateM.eval_f
        (Impl_Uint.run_wrapping_add BITS LIMBS x1 x2)
        stack 🌲
      (
        Output.Success (wrapping_add x1 x2),
        stack
      )
    }}.
  Admitted.

  Definition wrapping_sub {BITS LIMBS : usize} (x1 x2 : lib.Uint.t BITS LIMBS) :
      lib.Uint.t BITS LIMBS :=
    {| lib.Uint.value := (x1.(lib.Uint.value) - x2.(lib.Uint.value)) mod (2 ^ BITS.(Integer.value)) |}.

  Lemma wrapping_sub_eq (stack : Stack.t)
      (BITS LIMBS : usize) (x1 x2 : lib.Uint.t BITS LIMBS) :
    {{
      SimulateM.eval_f
        (Impl_Uint.run_wrapping_sub BITS LIMBS x1 x2)
        stack 🌲
      (
        Output.Success (wrapping_sub x1 x2),
        stack
      )
    }}.
  Admitted.
End Impl_Uint.
