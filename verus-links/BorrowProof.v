Require Import BorrowLink BridgeContract.
Theorem checked_execution : execution_claim pre post.
Proof.
  intros o _. destruct o as [[l r] sentinel]. split; [execute|].
  intro later. repeat eexists; repeat split; reflexivity.
Qed.
