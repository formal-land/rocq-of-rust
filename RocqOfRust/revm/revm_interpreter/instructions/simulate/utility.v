Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.simulate.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_interpreter.instructions.links.utility.

Module Impl_IntoAddress_for_U256.
  Definition into_address (self : aliases.U256.t) : Address.t :=
    Impl_Address.from_word (Impl_From_U256_for_FixedBytes_32.from self).

  Lemma into_address_eq (self : aliases.U256.t) (stack : Stack.t) :
    {{
      SimulateM.eval_f
        (Impl_IntoAddress_for_U256.run_into_address self)
        stack 🌲
      (Output.Success (into_address self), stack)
    }}.
  Proof.
  Admitted.
End Impl_IntoAddress_for_U256.
