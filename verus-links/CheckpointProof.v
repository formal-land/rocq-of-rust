Require Import CheckpointLink BridgeContract.
Theorem checked_execution : execution_claim pre post.
Proof.
  intros initial x _. exists x. split; [|reflexivity].
  repeat (cbn || get_can_access || eapply Run.Call || apply Run.LetUnfold || apply Run.Pure).
Qed.
