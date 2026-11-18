Require Import SwapLink BridgeContract.
Theorem checked_execution : execution_claim pre post.
Proof.
  intros o _. destruct o as [[l r] sentinel].
  exists {| Outer.pair := {| Pair.left := r; Pair.right := l |}; Outer.sentinel := sentinel |}.
  split; [execute | repeat split; reflexivity].
Qed.
