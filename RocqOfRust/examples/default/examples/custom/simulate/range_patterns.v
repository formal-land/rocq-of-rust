Require Import simulate.RocqOfRust.
Require Import examples.default.examples.custom.links.range_patterns.

Definition classify (x : u8) : u8 :=
  if BinOp.ge x {| Integer.value := 0 |} then
    if BinOp.le x {| Integer.value := 5 |} then
      {| Integer.value := 1 |}
    else
      {| Integer.value := 2 |}
  else
    {| Integer.value := 2 |}.

Lemma classify_eq (x : u8) :
  {{
    SimulateM.eval_f (run_classify x) []%stack 🌲
    (Output.Success (classify x), []%stack)
  }}.
Proof.
  destruct x as [x].
  unfold classify, BinOp.ge, BinOp.le; cbn.
  s.
  destruct (x >=? 0) eqn:Hge.
  { cbn.
    s.
    destruct (x <=? 5) eqn:Hle.
    { cbn. p. }
    { cbn. p. }
  }
  { cbn. p. }
Qed.

Example classify_zero :
  classify {| Integer.value := 0 |} = {| Integer.value := 1 |}.
Proof. reflexivity. Qed.

Example classify_five :
  classify {| Integer.value := 5 |} = {| Integer.value := 1 |}.
Proof. reflexivity. Qed.

Example classify_six :
  classify {| Integer.value := 6 |} = {| Integer.value := 2 |}.
Proof. reflexivity. Qed.
