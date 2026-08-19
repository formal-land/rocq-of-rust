Require Import simulate.RocqOfRust.
Require Import core.links.cmpOrdering.
Require Import core.intrinsics.links.mod.

Definition three_way_compare
    (integer_kind : IntegerKind.t)
    (x y : Integer.t integer_kind) :
    Ordering.t :=
  match Z.compare x.(Integer.value) y.(Integer.value) with
  | Lt => Ordering.Less
  | Eq => Ordering.Equal
  | Gt => Ordering.Greater
  end.

Lemma three_way_compare_eq
    (integer_kind : IntegerKind.t)
    (x y : Integer.t integer_kind)
    (stack : Stack.t) :
  {{
    SimulateM.eval_f
      (run_three_way_compare integer_kind x y)
      stack 🌲
    (
      Output.Success (three_way_compare integer_kind x y),
      stack
    )
  }}.
Proof.
Admitted.
