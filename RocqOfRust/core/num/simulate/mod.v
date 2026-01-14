Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import core.num.links.mod.

Module Impl_u64.
  Definition Self : Set := u64.

  Definition MIN : Self := {| Integer.value := 0 |}.

  Lemma min_eq (stack : Stack.t) :
    {{
      SimulateM.eval_f (Impl_u64.run_min) stack 🌲
      (Output.Success (Ref.immediate Pointer.Kind.Raw MIN), stack)
    }}.
  Proof.
    apply Run.Pure.
  Qed.

  Definition MAX : Self := {| Integer.value := 2 ^ 64 - 1 |}.

  Lemma max_eq (stack : Stack.t) :
    {{
      SimulateM.eval_f (Impl_u64.run_max) stack 🌲
      (Output.Success (Ref.immediate Pointer.Kind.Raw MAX), stack)
    }}.
  Proof.
    repeat (eapply Run.Call || apply Run.Pure).
  Qed.
End Impl_u64.
