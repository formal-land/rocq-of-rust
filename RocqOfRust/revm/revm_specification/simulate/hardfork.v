Require Import simulate.RocqOfRust.
Require Import revm.revm_specification.links.hardfork.

Module Impl_SpecId.
  Definition Self : Set := SpecId.t.

  Lemma get_discriminant_mod_256_eq (self : Self) :
    SpecId.get_discriminant self mod 256 = SpecId.get_discriminant self.
  Proof.
    destruct self; reflexivity.
  Qed.

  Definition is_enabled_in (self other : Self) : bool :=
    SpecId.get_discriminant self >=? SpecId.get_discriminant other.

  Lemma is_enabled_in_eq (stack : Stack.t) (self other : Self) :
    {{
      SimulateM.eval_f (Impl_SpecId.run_is_enabled_in self other) stack 🌲
      (Output.Success (is_enabled_in self other), stack)
    }}.
  Proof.
    unfold is_enabled_in; cbn.
    s; now rewrite get_discriminant_mod_256_eq.
  Qed.
End Impl_SpecId.
