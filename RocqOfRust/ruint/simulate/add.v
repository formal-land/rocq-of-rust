Require Import simulate.RocqOfRust.
Require Import core.ops.simulate.arith.
Require Import ruint.links.add.
Require Import ruint.links.lib.

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

  Definition wrapping_neg {BITS LIMBS : usize} (x : lib.Uint.t BITS LIMBS) :
      lib.Uint.t BITS LIMBS :=
    {| lib.Uint.value := (- x.(lib.Uint.value)) mod (2 ^ BITS.(Integer.value)) |}.

  Lemma wrapping_neg_eq (stack : Stack.t)
      (BITS LIMBS : usize) (x : lib.Uint.t BITS LIMBS) :
    {{
      SimulateM.eval_f
        (Impl_Uint.run_wrapping_neg BITS LIMBS x)
        stack 🌲
      (
        Output.Success (wrapping_neg x),
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

  Definition checked_sub {BITS LIMBS : usize} (x1 x2 : lib.Uint.t BITS LIMBS) :
      option (lib.Uint.t BITS LIMBS) :=
    if x2.(lib.Uint.value) <=? x1.(lib.Uint.value) then
      Some {| lib.Uint.value := x1.(lib.Uint.value) - x2.(lib.Uint.value) |}
    else
      None.

  Lemma checked_sub_eq (stack : Stack.t)
      (BITS LIMBS : usize) (x1 x2 : lib.Uint.t BITS LIMBS) :
    {{
      SimulateM.eval_f
        (Impl_Uint.run_checked_sub BITS LIMBS x1 x2)
        stack 🌲
      (
        Output.Success (checked_sub x1 x2),
        stack
      )
    }}.
  Admitted.
End Impl_Uint.

Module Impl_Add_for_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    lib.Uint.t BITS LIMBS.

  Definition add {BITS LIMBS : usize}
      (x y : Self BITS LIMBS) : Self BITS LIMBS :=
    Impl_Uint.wrapping_add x y.

  Global Instance I {BITS LIMBS : usize} :
      Add.C (Self BITS LIMBS) (Self BITS LIMBS) (Self BITS LIMBS) := {|
    Add.add := add;
  |}.

  Module Eq.
    Instance I {BITS LIMBS : usize} :
        Add.Eq.C (Self BITS LIMBS) (Self BITS LIMBS) (Self BITS LIMBS) I.
    Admitted.
  End Eq.
  Export (hints) Eq.
End Impl_Add_for_Uint.
Export (hints) Impl_Add_for_Uint.

Module Impl_Sub_for_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    lib.Uint.t BITS LIMBS.

  Definition sub {BITS LIMBS : usize}
      (x y : Self BITS LIMBS) : Self BITS LIMBS :=
    Impl_Uint.wrapping_sub x y.

  Global Instance I {BITS LIMBS : usize} :
      Sub.C (Self BITS LIMBS) (Self BITS LIMBS) (Self BITS LIMBS) := {|
    Sub.sub := sub;
  |}.

  Module Eq.
    Instance I {BITS LIMBS : usize} :
        Sub.Eq.C (Self BITS LIMBS) (Self BITS LIMBS) (Self BITS LIMBS) I.
    Admitted.
  End Eq.
  Export (hints) Eq.
End Impl_Sub_for_Uint.
Export (hints) Impl_Sub_for_Uint.
