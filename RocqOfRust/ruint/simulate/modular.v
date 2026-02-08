Require Import simulate.RocqOfRust.
Require Import ruint.links.modular.

Module Impl_Uint.
  Definition add_mod {BITS LIMBS : usize} (x1 x2 x3 : lib.Uint.t BITS LIMBS) :
      lib.Uint.t BITS LIMBS :=
    if x3.(lib.Uint.value) =? 0 then {| lib.Uint.value := 0 |}
    else {| lib.Uint.value := (x1.(lib.Uint.value) + x2.(lib.Uint.value)) mod x3.(lib.Uint.value) |}.

  Lemma add_mod_eq
      (stack : Stack.t)
      (BITS LIMBS : usize) (x1 x2 x3 : lib.Uint.t BITS LIMBS) :
    {{
      SimulateM.eval_f
        (Impl_Uint.run_add_mod BITS LIMBS x1 x2 x3)
        stack 🌲
      (
        Output.Success (add_mod x1 x2 x3),
        stack
      )
    }}.
  Admitted.

  Definition mul_mod {BITS LIMBS : usize} (x1 x2 x3 : lib.Uint.t BITS LIMBS) :
      lib.Uint.t BITS LIMBS :=
    if x3.(lib.Uint.value) =? 0 then {| lib.Uint.value := 0 |}
    else {| lib.Uint.value := (x1.(lib.Uint.value) * x2.(lib.Uint.value)) mod x3.(lib.Uint.value) |}.

  Lemma mul_mod_eq
      (stack : Stack.t)
      (BITS LIMBS : usize) (x1 x2 x3 : lib.Uint.t BITS LIMBS) :
    {{
      SimulateM.eval_f
        (Impl_Uint.run_mul_mod BITS LIMBS x1 x2 x3)
        stack 🌲
      (
        Output.Success (mul_mod x1 x2 x3),
        stack
      )
    }}.
  Admitted.
End Impl_Uint.
