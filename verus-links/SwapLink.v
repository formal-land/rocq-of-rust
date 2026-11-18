Require Export RocqOfRust.simulate.RocqOfRust NestedSupport Assertion.
Open Scope string_scope.
Import ListNotations.
Definition observed_paths := (nested_paths ++ [])%list.
Definition linked_function := "nested::swap".
Definition linked_site := "contract".
Definition execution_claim (P Q : observations -> Prop) :=
  forall initial : Outer.t,
    P (memory_view initial initial (fun _ _ => 0%Z)) ->
    exists final,
    {{ SimulateM.eval_f (run_swap root) [initial]%stack 🌲 (Output.Success tt, [final]%stack) }} /\
    Q (memory_view initial final (fun _ _ => 0%Z)).
