Require Import simulate.RocqOfRust.
Require Import core.num.simulate.mod.
Require Import revm.revm_interpreter.interpreter.links.shared_memory.

Definition num_words (len : usize) : usize :=
  Impl_usize.saturating_add len 31 /i 32.

Lemma num_words_eq (len : usize) (stack : Stack.t) :
  {{
    SimulateM.eval_f (run_num_words len) stack 🌲
    (Output.Success (num_words len), stack)
  }}.
Proof.
  with_strategy transparent [run_num_words] unfold run_num_words.
  s. {
    apply Impl_usize.saturating_add_eq.
  }
  s.
Qed.
