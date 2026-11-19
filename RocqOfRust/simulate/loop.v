Require Import simulate.RocqOfRust.
From Stdlib Require Import Lia.

(** A loop can expose its counter through an indexed family of stack states.
    This allows the proof to describe locals above any caller frame. *)
Lemma run_loop_steps {R B A : Set}
    (body : Stack.t -> SimulateM.t (Output.t R B * Stack.t))
    (on_exit : Output.Exception.t R -> Stack.t -> SimulateM.t A)
    (state : nat -> Stack.t) (value : A) (first limit : nat) :
  (first <= limit)%nat ->
  (forall j, (first <= j < limit)%nat -> exists iteration,
    {{ body (state j) 🌲 (Output.Success iteration, state (S j)) }}) ->
  {{ SimulateM.Loop body (state limit) on_exit 🌲 value }} ->
  {{ SimulateM.Loop body (state first) on_exit 🌲 value }}.
Proof.
  intros Hle step exit.
  remember (limit-first)%nat as count eqn:E. revert first E Hle step.
  induction count as [|count IH]; intros first E Hle step.
  - replace first with limit by lia. exact exit.
  - destruct (step first ltac:(lia)) as [iteration iteration_exec].
    eapply Run.LoopNext; [exact iteration_exec |].
    apply IH; [lia | lia |]. intros j Hj. apply step. lia.
Qed.
