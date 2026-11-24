Require Export RocqOfRust.simulate.RocqOfRust.
Require Export Assertion checkpoint.
Open Scope string_scope.

Definition linked_function := "checkpoint::set_word".
Definition linked_site := "assert_0".
Definition linked_source_sha256 := "40548e469b95fbb125744699c6e967b19b92199393fe978ab85be0c81a4914cb".
Definition observed_paths := [WordPath Current ["p"]; WordPath Current ["x"]].

Definition set_run (p : '&mut u32) (x : u32) :
  Run.Trait set_word [] [] [φ p; φ x] unit.
Proof. constructor; run_symbolic. Defined.

(** The selected proof block follows the last Rust statement. Current p is
    therefore the value in the final stack slot. The source digest anchors
    that cutpoint even if moving the ghost assertion leaves erasure unchanged. *)
Definition at_point (p x : u32) : observations :=
  {| word_at _ path := match path with
       | ["p"] => p.(Integer.value) | ["x"] => x.(Integer.value) | _ => 0 end;
     slice_at := fun _ _ => [] |}.

Definition execution_claim (P Q : observations -> Prop) :=
  forall initial x : u32,
    P (at_point initial x) ->
    exists final : u32,
    {{ SimulateM.eval_f (set_run (make_ref 0) x) [initial]%stack 🌲
        (Output.Success tt, [final]%stack) }} /\ Q (at_point final x).
