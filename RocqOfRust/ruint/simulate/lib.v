Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import ruint.links.lib.

Module Impl_Uint.
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  Parameter from_limbs :
    forall {BITS LIMBS : Usize.t} (limbs : array.t U64.t LIMBS),
    Self BITS LIMBS.

  Lemma from_limbs_eq
      (stack : Stack.t)
      (BITS LIMBS : Usize.t) (limbs : array.t U64.t LIMBS) :
    {{
      SimulateM.eval_f
        (Impl_Uint.run_from_limbs BITS LIMBS limbs)
        stack 🌲
      (
        Output.Success (from_limbs limbs),
        stack
      )
    }}.
  Admitted.

  Parameter BITS :
    forall (BITS LIMBS : Usize.t),
    Usize.t.

  Lemma BITS_eq
      (stack : Stack.t)
      (BITS LIMBS : Usize.t) :
    {{
      SimulateM.eval_f
        (Impl_Uint.run_BITS BITS LIMBS)
        stack 🌲
      (
        Output.Success (Ref.immediate Pointer.Kind.Raw BITS),
        stack
      )
    }}.
  Admitted.

  Parameter ZERO :
    forall {BITS LIMBS : Usize.t},
    Self BITS LIMBS.

  Lemma ZERO_eq
      (stack : Stack.t)
      (BITS LIMBS : Usize.t) :
    {{
      SimulateM.eval_f
        (Impl_Uint.run_ZERO BITS LIMBS)
        stack 🌲
      (
        Output.Success (Ref.immediate Pointer.Kind.Raw ZERO),
        stack
      )
    }}.
  Admitted.

  Parameter MIN :
    forall {BITS LIMBS : Usize.t},
    Self BITS LIMBS.

  Lemma MIN_eq
      (stack : Stack.t)
      (BITS LIMBS : Usize.t) :
    {{
      SimulateM.eval_f
        (Impl_Uint.run_MIN BITS LIMBS)
        stack 🌲
      (
        Output.Success (Ref.immediate Pointer.Kind.Raw MIN),
        stack
      )
    }}.
  Admitted.

  Parameter MAX :
    forall {BITS LIMBS : Usize.t},
    Self BITS LIMBS.

  Lemma MAX_eq
      (stack : Stack.t)
      (BITS LIMBS : Usize.t) :
    {{
      SimulateM.eval_f
        (Impl_Uint.run_MAX BITS LIMBS)
        stack 🌲
      (
        Output.Success (Ref.immediate Pointer.Kind.Raw MAX),
        stack
      )
    }}.
  Admitted.
End Impl_Uint.
