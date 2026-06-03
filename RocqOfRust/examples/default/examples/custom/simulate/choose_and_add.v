Require Import simulate.RocqOfRust.
Require Import examples.default.examples.custom.links.choose_and_add.

Definition choose_u32 (take_left : bool) (x y : u32) : u32 :=
  if take_left then x else y.

Definition add_pair (pair : u32 * u32) : u32 :=
  let '(x, y) := pair in
  x +i y.

Definition choose_and_add
   (take_left : bool) 
   (pair : u32 * u32)
   (offset : u32) :
   u32 :=
 let '(x, y) := pair in
 let selected := choose_u32 take_left x y in
 selected +i offset.

 Lemma choose_u32_eq (take_left : bool) (x y : u32) :
  {{
    SimulateM.eval_f (run_choose_u32 take_left x y) []%stack 🌲
    (Output.Success (choose_u32 take_left x y), []%stack)
  }}.
Proof.
  unfold choose_u32.
  destruct take_left; s.
Qed.

Lemma add_pair_eq (pair : u32 * u32) :
  {{
    SimulateM.eval_f (run_add_pair pair) []%stack 🌲
    (Output.Success (add_pair pair), []%stack)
  }}.
Proof.
  destruct pair as [x y].
  unfold add_pair; cbn.
  with_strategy transparent [run_add_pair] cbn.
  repeat (
    cbn ||
    get_can_access ||
    eapply Run.Call ||
    apply Run.Pure
  ).
Qed.

Lemma choose_and_add_eq
    (take_left : bool)
    (pair : u32 * u32)
    (offset : u32) :
  {{
    SimulateM.eval_f (run_choose_and_add take_left pair offset) []%stack 🌲
    (Output.Success (choose_and_add take_left pair offset), []%stack)
  }}.
 Proof.
  destruct pair as [x y].
  unfold choose_and_add; cbn.
  with_strategy transparent [run_choose_and_add] cbn.
  repeat (
    cbn ||
    get_can_access ||
    apply Run.LetUnfold
  ).
  eapply Run.Call.
  { apply choose_u32_eq. }
  repeat (
    cbn ||
    get_can_access ||
    apply Run.LetUnfold ||
    eapply Run.Call ||
    apply Run.Pure
  ).
 Qed.  
   