Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed.

Module Impl_Address.
  Definition Self : Set :=
    Address.t.

  Parameter from_word : FixedBytes.t {| Integer.value := 32 |} -> Self.

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
