Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.bits.simulate.fixed.

Module Impl_Address.
  Definition Self : Set :=
    Address.t.

  Definition from_word (value : FixedBytes.t {| Integer.value := 32 |}) : Self :=
    {| Address.value := FixedBytes.to_Z value mod (2^160) |}.

  Lemma from_word_eq (value : FixedBytes.t {| Integer.value := 32 |}) (stack : Stack.t) :
    {{
      SimulateM.eval_f
        (Impl_Address.run_from_word value)
        stack 🌲
      (
        Output.Success (from_word value),
        stack
      )
    }}.
  Admitted.

  Definition into_word (self : Self) : FixedBytes.t {| Integer.value := 32 |} :=
    FixedBytes.from_Z self.(Address.value).

  Lemma into_word_eq (ref_self : '& Self) (self : Self) (stack : Stack.t) :
    CanRead.t stack self ref_self ->
    {{
      SimulateM.eval_f
        (Impl_Address.run_into_word ref_self)
        stack 🌲
      (Output.Success (into_word self), stack)
    }}.
  Admitted.
End Impl_Address.
