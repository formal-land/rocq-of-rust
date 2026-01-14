Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import RocqOfRust.lib.simulate.lib.
Require Import core.links.array.
Require Import examples.default.examples.custom.links.loops_free.

Definition max2 (a b : u32) : u32 :=
  if a.(Integer.value) <? b.(Integer.value) then
    b
  else
    a.

Lemma max2_eq (stack : Stack.t) (a b : u32) :
  {{
    SimulateM.eval_f (run_max2 a b) stack 🌲
    (Output.Success (max2 a b), stack)
  }}.
Proof.
  unfold max2.
  repeat (
    cbn ||
    get_can_access ||
    eapply Run.Call ||
    apply Run.Pure ||
    destruct (_ <? _)
  ).
Qed.

Definition abs_i32 (x : i32) : i32 :=
  if x.(Integer.value) <? 0 then
    if x.(Integer.value) =? (-(2 ^ 31)) then
      x
    else
      {| Integer.value := - x.(Integer.value) |}
  else
    x.

Lemma abs_i32_eq (stack : Stack.t) (x : i32) :
  {{
    SimulateM.eval_f (run_abs_i32 x) stack 🌲
    (Output.Success (abs_i32 x), stack)
  }}.
Proof.
  unfold abs_i32; cbn.
  eapply Run.Call. { apply Run.Pure. } cbn.
  eapply Run.Call. { apply Run.Pure. } cbn.
  destruct (_ <? 0); cbn.
  { eapply Run.Call. { apply Run.Pure. } cbn.
    destruct (_ =? _); cbn; apply Run.Pure.
  }
  { apply Run.Pure. }
Qed.

Definition bool_and (a b : bool) : bool :=
  if a
  then if b then true else false
  else false.

Lemma bool_and_eq (stack : Stack.t) (a b : bool) :
  {{
    SimulateM.eval_f (run_bool_and a b) stack 🌲
    (Output.Success (bool_and a b), stack)
  }}.
Proof.
  unfold bool_and.
  repeat (
    cbn ||
    get_can_access ||
    eapply Run.Call ||
    apply Run.Pure ||
    destruct a ||
    destruct b
  ).
Qed.

Definition get_or_zero (xs : array.t u32 {| Integer.value := 4 |}) (i : usize) : u32 :=
  let i := i.(Integer.value) in
  let xs := ArrayPairs.to_tuple_rev xs.(array.value) in
  match xs with
  | (tt, x3, x2, x1, x0) =>
    if i =? 0 then
      x0
    else if i =? 1 then
      x1
    else if i =? 2 then
      x2
    else if i =? 3 then
      x3
    else
      {| Integer.value := 0 |}
  end.

Lemma get_or_zero_eq
    (xs : array.t u32 4) (i : usize)
    (H_i : 0 <= i.(Integer.value)) :
  let ref_xs := make_ref 0 in
  let stack := [xs]%stack in
  {{
    SimulateM.eval_f (run_get_or_zero ref_xs i) stack 🌲
    (Output.Success (get_or_zero xs i), stack)
  }}.
Proof.
  destruct xs as [[x0 [x1 [x2 [x3 []]]]]].
  destruct i as [i]; cbn in H_i.
  unfold get_or_zero; cbn.
  eapply Run.Call; cbn. { apply Run.Pure. } cbn.
  eapply Run.Call; cbn. { apply Run.Pure. } cbn.
  destruct (_ <? 4) eqn:HeqBound; cbn.
  { progress repeat get_can_access.
    unfold ArrayPairs.to_tuple_rev, Pos.to_nat; cbn.
    destruct (i =? 0) eqn:Hi0. { replace i with 0 by lia; cbn; apply Run.Pure. }
    destruct (i =? 1) eqn:Hi1. { replace i with 1 by lia; cbn; apply Run.Pure. }
    destruct (i =? 2) eqn:Hi2. { replace i with 2 by lia; cbn; apply Run.Pure. }
    destruct (i =? 3) eqn:Hi3. { replace i with 3 by lia; cbn; apply Run.Pure. }
    lia.
  }
  { unfold ArrayPairs.to_tuple_rev, Pos.to_nat; cbn.
    destruct (i =? 0) eqn:Hi0; [lia|].
    destruct (i =? 1) eqn:Hi1; [lia|].
    destruct (i =? 2) eqn:Hi2; [lia|].
    destruct (i =? 3) eqn:Hi3; [lia|].
    apply Run.Pure.
  }
Qed.

Definition eq2 (a b : array.t u32 {| Integer.value := 2 |}) : bool :=
  let '(tt, x1, x0) := ArrayPairs.to_tuple_rev a.(array.value) in
  let '(tt, y1, y0) := ArrayPairs.to_tuple_rev b.(array.value) in
  if (x0.(Integer.value) =? y0.(Integer.value)) &&
     (x1.(Integer.value) =? y1.(Integer.value))
  then true
  else false.

Lemma eq2_eq
    (a b : array.t u32 {| Integer.value := 2 |}) :
  let ref_a := make_ref 0 in
  let ref_b := make_ref 1 in
  let stack := [a; b]%stack in
  {{
    SimulateM.eval_f (run_eq2 ref_a ref_b) stack 🌲
    (Output.Success (eq2 a b), stack)
  }}.
Proof.
  destruct a as [[[a0] [[a1] []]]].
  destruct b as [[[b0] [[b1] []]]].
  unfold eq2; cbn.
  get_can_access.
  get_can_access.
  eapply Run.Call. { apply Run.Pure. } cbn.
  destruct (_ =? _); cbn.
  { progress repeat get_can_access.
    eapply Run.Call. { apply Run.Pure. } cbn.
    eapply Run.Call. { apply Run.Pure. } cbn.
    destruct (_ =? _); cbn; apply Run.Pure.
  }
  { eapply Run.Call. { apply Run.Pure. } cbn.
    apply Run.Pure.
  }
Qed.

Definition eq_pair (x y : u32 * u32) : bool :=
  let '(x0, x1) := x in
  let '(y0, y1) := y in
  if (x0.(Integer.value) =? y0.(Integer.value)) &&
     (x1.(Integer.value) =? y1.(Integer.value))
  then true
  else false.

Lemma eq_pair_eq (stack : Stack.t) (x y : u32 * u32) :
  {{
    SimulateM.eval_f (run_eq_pair x y) stack 🌲
    (Output.Success (eq_pair x y), stack)
  }}.
Proof.
  destruct x as [x0 x1]; destruct y as [y0 y1].
  unfold eq_pair; cbn.
  eapply Run.Call. { apply Run.Pure. } cbn.
  destruct (_ =? _); cbn.
  { eapply Run.Call. { apply Run.Pure. } cbn.
    eapply Run.Call. { apply Run.Pure. } cbn.
    destruct (_ =? _); cbn; apply Run.Pure.
  }
  { eapply Run.Call. { apply Run.Pure. } cbn.
    apply Run.Pure.
  }
Qed.

Definition min3 (a b c : u32) : u32 :=
  let m := if a.(Integer.value) <? b.(Integer.value) then a else b in
  if m.(Integer.value) <? c.(Integer.value) then m else c.

Lemma min3_eq (a b c : u32) :
  {{
    SimulateM.eval_f (run_min3 a b c) []%stack 🌲
    (Output.Success (min3 a b c), []%stack)
  }}.
Proof.
  destruct a as [a]; destruct b as [b]; destruct c as [c].
  unfold min3; cbn.
  eapply Run.Call. { apply Run.Pure. } cbn.
  eapply Run.Call. { apply Run.Pure. } cbn.
  destruct (a <? b); cbn.
  { get_can_access.
    eapply Run.Call. { apply Run.Pure. } cbn.
    eapply Run.Call. { apply Run.Pure. } cbn.
    destruct (a <? c); cbn.
    { get_can_access.
      apply Run.Pure.
    }
    { apply Run.Pure. }
  }
  { get_can_access.
    eapply Run.Call. { apply Run.Pure. } cbn.
    eapply Run.Call. { apply Run.Pure. } cbn.
    destruct (b <? c); cbn.
    { get_can_access.
      apply Run.Pure.
    }
    { apply Run.Pure. }
  }
Qed.

Definition choose_ref (choice : bool) (a b : u32) : u32 :=
  if choice then
    a
  else
    b.

Lemma choose_ref_eq (choice : bool) (a b : u32) :
  let stack := [a; b]%stack in
  let ref_a := make_ref 0 in
  let ref_b := make_ref 1 in
  {{
    SimulateM.eval_f (run_choose_ref choice ref_a ref_b) stack 🌲
    (Output.Success (choose_ref choice a b), stack)
  }}.
Proof.
  unfold choose_ref; cbn.
  eapply Run.Call; cbn. {
    apply Run.Pure.
  }
  cbn.
  destruct choice; cbn.
  { get_can_access.
    apply Run.Pure.
  }
  { get_can_access.
    apply Run.Pure.
  }
Qed.
