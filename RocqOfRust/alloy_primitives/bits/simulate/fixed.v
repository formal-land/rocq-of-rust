Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Export alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.links.aliases.

Module Impl_From_U256_for_FixedBytes_32.
  Definition Self : Set :=
    FixedBytes.t {| Integer.value := 32 |}.

  Parameter from : aliases.U256.t -> Self.

  Lemma from_eq (value : aliases.U256.t) (stack : Stack.t) :
    {{
      SimulateM.eval_f
        (Impl_From_U256_for_FixedBytes_32.run_from value)
        stack 🌲
      (
        Output.Success (from value),
        stack
      )
    }}.
  Admitted.
End Impl_From_U256_for_FixedBytes_32.
