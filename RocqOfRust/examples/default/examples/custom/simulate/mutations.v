Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import core.links.option.
Require Import examples.default.examples.custom.links.mutations.

Module Option.
  Definition unwrap_or {A : Set} (value : option A) (default : A) : A :=
    match value with
    | Some value => value
    | None => default
    end.

  Lemma unwrap_or_eq {A : Set} `{Link A} (value : option A) (default : A) :
    {{
      SimulateM.eval_f (run_unwrap_or value default) []%stack 🌲
      (Output.Success (unwrap_or value default), []%stack)
    }}.
  Proof.
    destruct value;
      repeat (
        cbn ||
        get_can_access ||
        apply Run.Pure
      ).
  Qed.
End Option.

Definition apply_duplicate (numbers : Numbers.t) : Numbers.t :=
  {|
    Numbers.a := numbers.(Numbers.a);
    Numbers.b := numbers.(Numbers.a);
    Numbers.c := numbers.(Numbers.a);
  |}.

Lemma apply_duplicate_eq (numbers : Numbers.t) :
  let ref_numbers :=
    {| Ref.core := Ref.Core.Mutable (A := Numbers.t) 0%nat [] φ Some (fun _ => Some) |} in
  {{
    SimulateM.eval_f (run_apply_duplicate ref_numbers) [numbers]%stack 🌲
    (Output.Success tt, [apply_duplicate numbers]%stack)
  }}.
Proof.
  with_strategy transparent [
    run_apply_duplicate
    run_get_a_ref
    run_get_b_mut
  ] cbn.
  repeat (
    cbn ||
    get_can_access ||
    eapply Run.Call ||
    apply Run.Pure
  ).
Qed.

Lemma duplicate_eq (a b c : U64.t) :
  let ref_a := make_ref 0 in
  let ref_b := make_ref 1 in
  let ref_c := make_ref 2 in
  {{
    SimulateM.eval_f (run_duplicate ref_a ref_b ref_c) [a; b; c]%stack 🌲
    (Output.Success tt, [a; a; a]%stack)
  }}.
Proof.
  repeat (
    cbn ||
    get_can_access ||
    eapply Run.Call ||
    apply Run.Pure
  ).
Qed.
