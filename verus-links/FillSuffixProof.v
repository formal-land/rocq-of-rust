Require Import FillSuffixLink FillProof BridgeContract.
Theorem checked_execution : FillSuffixLink.execution_claim pre post.
Proof.
  intros xs n v frame Hn Hpre.
  destruct (FillProof.checked_execution xs n v frame Hn Hpre) as [final [run [_ [_ suffix]]]].
  exists final. split; assumption.
Qed.
