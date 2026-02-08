Require Import simulate.RocqOfRust.
Require Import examples.default.examples.custom.links.fosdem.

Definition MAX_VALUE : u64 := {| Integer.value := 1000 |}.

Lemma MAX_VALUE_eq (stack : Stack.t) :
  {{
    SimulateM.eval_f run_MAX_VALUE stack 🌲
    (Output.Success (Ref.immediate Pointer.Kind.Raw MAX_VALUE), stack)
  }}.
Proof.
  s.
Qed.

Definition increment (counter : Counter.t) (amount : u64) : Counter.t :=
  if counter.(Counter.value) +i amount >i MAX_VALUE then
    counter <| Counter.value := MAX_VALUE |>
  else
    counter <| Counter.value := counter.(Counter.value) +i amount |>.

Lemma increment_eq (counter : Counter.t) (amount : u64) :
  let ref_counter := make_ref 0 in
  {{
    SimulateM.eval_f (run_increment ref_counter amount) [counter]%stack 🌲
    (Output.Success tt, [increment counter amount]%stack)
  }}.
Proof.
  unfold increment.
  s.
  unfold ">i"; cbn.
  destruct (_ >? _); s.
Qed.

Definition CounterSmallerThanMAX_VALUE (counter : Counter.t) : Prop :=
  i[counter.(Counter.value)] <= i[MAX_VALUE].

Lemma counter_stays_smaller_than_MAX_VALUE (counter : Counter.t) (amount : u64) :
  CounterSmallerThanMAX_VALUE counter ->
  CounterSmallerThanMAX_VALUE (increment counter amount).
Proof.
  destruct counter as [value].
  destruct value as [value], amount as [amount].
  unfold CounterSmallerThanMAX_VALUE, increment, ">i"; cbn.
  intros.
  destruct (_ >? _) eqn:?; cbn; lia.
Qed.
