Require Import links.RocqOfRust.
Require Import RocqOfRust.simulate.M.
Require Import RocqOfRust.lib.simulate.lib.
Require Import core.links.array.
Require Import ruint.links.lib.

Module Impl_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  Parameter from_limbs :
    forall {BITS LIMBS : usize} (limbs : array.t u64 LIMBS),
    Self BITS LIMBS.

  Lemma from_limbs_eq
      (stack : Stack.t)
      (BITS LIMBS : usize) (limbs : array.t u64 LIMBS) :
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
    forall (BITS LIMBS : usize),
    usize.

  Lemma BITS_eq
      (stack : Stack.t)
      (BITS LIMBS : usize) :
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

  Definition ZERO {BITS LIMBS : usize} : Self BITS LIMBS :=
    {| Uint.value := 0 |}.

  Lemma ZERO_eq
      (stack : Stack.t)
      (BITS LIMBS : usize) :
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

  Definition MIN {BITS LIMBS : usize} : Self BITS LIMBS :=
    {| Uint.value := 0 |}.

  Lemma MIN_eq
      (stack : Stack.t)
      (BITS LIMBS : usize) :
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

  Definition MAX {BITS LIMBS : usize} : Self BITS LIMBS :=
    {| Uint.value := 2 ^ 256 - 1 |}.

  Lemma MAX_eq
      (stack : Stack.t)
      (BITS LIMBS : usize) :
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

  Definition as_limbs (self : Self 256 4) : array.t u64 4 :=
    {|
      array.value := ArrayPairs.of_list [
        self.(Uint.value) mod (2 ^ 64) : u64;
        (self.(Uint.value) / (2 ^ 64)) mod (2 ^ 64) : u64;
        (self.(Uint.value) / (2 ^ 128)) mod (2 ^ 64) : u64;
        (self.(Uint.value) / (2 ^ 192)) : u64
      ] : ArrayPairs.t _ (Z.to_nat (i[4]));
    |}.

  Lemma as_limbs_eq
      (stack : Stack.t)
      (ref_self : '& (Self 256 4))
      (self : Self 256 4) :
    CanRead.t stack self ref_self ->
    {{
      SimulateM.eval_f
        (Impl_Uint.run_as_limbs 256 4 ref_self)
        stack 🌲
      (
        Output.Success (Ref.immediate _ (as_limbs self)),
        stack
      )
    }}.
  Admitted.
End Impl_Uint.
