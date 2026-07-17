Require Import simulate.RocqOfRust.
Require Import examples.default.examples.custom.links.tuple_assignment.
From Stdlib Require Import Program.Equality.

Definition rust_result : u64 * u64 :=
  ({| Integer.value := 4 |}, {| Integer.value := 5 |}).

Lemma tuple_assignment_does_not_simulate_rust :
  ~
  {{
    SimulateM.eval_f run_tuple_assignment []%stack 🌲
    (Output.Success rust_result, []%stack)
  }}.
Proof.
  with_strategy transparent [run_tuple_assignment] cbn.
  intros H.
  repeat match goal with
  | H_run : Run.t _ _ |- _ => dependent destruction H_run
  | H_access : Stack.CanAccess.t _ (Ref.Core.Immediate _) |- _ => inversion H_access
  end.
Qed.
