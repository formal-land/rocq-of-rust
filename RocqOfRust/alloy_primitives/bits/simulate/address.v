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
End Impl_Address.
