Require Import RocqOfRust.simulate.RocqOfRust.
Require Import Assertion SliceIndex FillLink BridgeContract.
Open Scope Z_scope.

Definition filled (xs : list u32) (v : u32) (i : nat) :=
  (List.repeat v i ++ List.skipn i xs)%list.

Lemma filled_length xs v i :
  (i <= List.length xs)%nat -> List.length (filled xs v i) = List.length xs.
Proof.
  unfold filled. rewrite List.length_app, List.repeat_length, List.length_skipn. lia.
Qed.

Lemma filled_inside xs v i j :
  (j < i)%nat -> List.nth_error (filled xs v i) j = Some v.
Proof.
  intros H. unfold filled. rewrite List.nth_error_app1 by (rewrite List.repeat_length; lia).
  apply List.nth_error_repeat. assumption.
Qed.

Lemma filled_outside xs v i j :
  (i <= j)%nat -> List.nth_error (filled xs v i) j = List.nth_error xs j.
Proof.
  intro H. unfold filled. rewrite List.nth_error_app2 by (rewrite List.repeat_length; lia).
  rewrite List.repeat_length, List.nth_error_skipn. f_equal. lia.
Qed.

Lemma filled_update xs v i :
  (i < List.length xs)%nat ->
  SliceIndex.update (filled xs v i) i v = Some (filled xs v (S i)).
Proof.
  revert xs. induction i as [|i IH]; intros [|x xs] H; cbn in H; try lia.
  - reflexivity.
  - change (SliceIndex.update (v :: filled xs v i) (S i) v = Some (v :: filled xs v (S i))).
    specialize (IH xs ltac:(lia)).
    unfold SliceIndex.update in *. cbn.
    destruct (List.nth_error (filled xs v i) i); [|discriminate].
    injection IH as E. now rewrite E.
Qed.

Definition counter (i : nat) : usize := {| Integer.value := Z.of_nat i |}.

Lemma write_counter {A : Set} (frame : Stack.t) (old new : A) :
  Stack.write (Stack.nth_alloc frame old) new = Stack.alloc frame new.
Proof.
  induction frame as [|B b frame IH]; [reflexivity|].
  change (Stack.Cons b (Stack.write (Stack.nth_alloc frame old) new) =
          Stack.Cons b (Stack.alloc frame new)).
  now rewrite IH.
Qed.

Ltac fill_access :=
  unshelve eapply Run.GetCanAccess;
  [ eapply Stack.CanAccess.Mutable;
    first [apply Stack.Nth.ConsZero | apply Stack.Nth.ConsSucc;
      repeat first [apply Stack.nth_alloc | apply Stack.nth_alloc_alloc]] | ].

Lemma fill_execution (xs : list u32) (v : u32) (n : nat) (frame : Stack.t) :
  (n <= List.length xs)%nat -> Z.of_nat n < 2^64 ->
  {{ SimulateM.eval_f (fill_run (make_ref 0) (counter n) v) (xs :: frame)%stack 🌲
     (Output.Success tt, (filled xs v n :: frame)%stack) }}.
Proof.
  intros Hlen Hword.
  repeat (cbn || eapply Run.Call || apply Run.LetUnfold || apply Run.Pure).
  lazymatch goal with |- Run.t _ (SimulateM.Loop ?b _ ?k) =>
    set (body := b); set (finish := k)
  end.
  assert (execute : forall remaining i, (i + remaining = n)%nat ->
     {{ SimulateM.Loop body (filled xs v i :: Stack.alloc frame (counter i))%stack finish 🌲
        (Output.Success tt, (filled xs v n :: frame)%stack) }}).
  { induction remaining as [|remaining IH]; intros i Hi.
    - assert (i = n) by lia. subst i.
      eapply Run.LoopExit with (exit := Output.Exception.Break)
        (next := (filled xs v n :: Stack.alloc frame (counter n))%stack).
      + unfold body.
        repeat (cbn || fill_access || rewrite Stack.read_nth_alloc_eq || rewrite Z.ltb_irrefl ||
          eapply Run.Call || apply Run.LetUnfold || apply Run.Pure).
      + unfold finish.
        change ({{ SimulateM.Pure (Output.Success (R := unit) tt,
          Stack.dealloc (Stack.alloc (filled xs v n :: frame)%stack (counter n))) 🌲
          (Output.Success tt, (filled xs v n :: frame)%stack) }}).
        rewrite Stack.dealloc_alloc_eq. apply Run.Pure.
    - assert (test : (Z.of_nat i <? Z.of_nat n) = true) by (apply Z.ltb_lt; lia).
      assert (step : (Z.of_nat i + 1) mod 2^64 = Z.of_nat (S i)).
      { rewrite Z.mod_small by lia. lia. }
      pose proof (filled_update xs v i ltac:(lia)) as write.
      eapply Run.LoopStep with (item := tt)
        (next := (filled xs v (S i) :: Stack.alloc frame (counter (S i)))%stack).
      + unfold body.
        repeat (cbn || fill_access || rewrite Stack.read_nth_alloc_alloc ||
          rewrite Stack.write_nth_alloc_alloc || rewrite Stack.read_nth_alloc_eq || rewrite write_counter ||
          rewrite test || rewrite Nat2Z.id || setoid_rewrite write || rewrite step ||
          eapply Run.Call || apply Run.LetUnfold || apply Run.Pure).
        change ({{ SimulateM.Pure (Output.Success (R := unit) tt,
          Stack.dealloc (Stack.dealloc (Stack.alloc (Stack.alloc
            (filled xs v (S i) :: Stack.alloc frame (counter (S i)))%stack tt) tt))) 🌲
          (Output.Success tt, (filled xs v (S i) :: Stack.alloc frame (counter (S i)))%stack) }}).
        rewrite !Stack.dealloc_alloc_eq. apply Run.Pure.
      + apply IH. lia.
  }
  exact (execute n 0%nat eq_refl).
Qed.

Lemma fill_post xs v n :
  (n <= List.length xs)%nat ->
  contract_post (fill_observations xs (filled xs v n) (filled xs v n) (counter n) v (Z.of_nat n)).
Proof.
  intro Hn. cbn. rewrite !List.length_map, filled_length by assumption.
  split; [reflexivity|]. split; intros z Hz.
  - unfold lookup. assert (test : (z <? 0) = false) by (apply Z.ltb_ge; lia). rewrite test.
    rewrite List.nth_error_map, filled_inside by lia. reflexivity.
  - unfold lookup. assert (test : (z <? 0) = false) by (apply Z.ltb_ge; lia). rewrite test.
    rewrite !List.nth_error_map, filled_outside by lia.
    destruct (List.nth_error xs (Z.to_nat z)) eqn:E.
    + cbn. change (@List.nth_error (Integer.t IntegerKind.U32) xs (Z.to_nat z) = Some u) in E.
      now rewrite E.
    + apply List.nth_error_None in E.
      change (Z.of_nat n <= z < Z.of_nat (List.length xs)) in Hz. lia.
Qed.

Theorem checked_execution : execution_claim pre contract_post.
Proof.
  intros xs [bound] v frame Hrange Hpre.
  cbn in Hpre. rewrite List.length_map in Hpre.
  change (0 <= bound < 2^64) in Hrange.
  change (bound <= Z.of_nat (List.length xs)) in Hpre.
  set (n := Z.to_nat bound).
  assert (Hrepr : Z.of_nat n = bound) by (unfold n; lia).
  assert (Hn : (n <= List.length xs)%nat) by lia.
  exists (filled xs v n). rewrite <- Hrepr.
  split; [apply fill_execution; lia | apply fill_post; assumption].
Qed.
