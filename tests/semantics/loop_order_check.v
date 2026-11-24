Require Import RocqOfRust.simulate.RocqOfRust ReleaseTests.loop_order.

Instance run_digits : Run.Trait digits [] [] [] u32.
Proof. constructor. run_symbolic. Defined.

Example digits_in_source_order :
  {{ SimulateM.eval_f run_digits []%stack 🌲
     (Output.Success ({| Integer.value := 12 |} : u32), []%stack) }}.
Proof.
  Ltac advance := repeat first [apply Run.Pure | get_can_access | apply Run.LetUnfold |
                                eapply Run.Call | progress cbn].
  advance. do 3 (eapply Run.LoopNext; [solve [advance]|]).
  eapply Run.LoopExit; solve [advance].
Qed.
