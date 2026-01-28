Require Import simulate.RocqOfRust.
Require Import examples.default.examples.custom.links.add_one.

Definition add_one (x : u32) : u32 :=
  x +i 1.

Lemma add_one_eq (x : u32) :
  {{
    SimulateM.eval_f (run_add_one x) []%stack 🌲
    (Output.Success (add_one x), []%stack)
  }}.
Proof.
  repeat (
    eapply Run.Call ||
    apply Run.Pure
  ).
Qed.
