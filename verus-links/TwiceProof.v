Require Import TwiceLink BridgeContract.
Theorem checked_execution : execution_claim pre post.
Proof.
  intros o a b _. destruct o as [[l r] sentinel].
  exists {| Outer.pair := {| Pair.left := b; Pair.right := r |}; Outer.sentinel := sentinel |}.
  split; [execute | repeat split; reflexivity].
Qed.
