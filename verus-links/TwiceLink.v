Require Export RocqOfRust.simulate.RocqOfRust NestedSupport Assertion.
Import ListNotations.
Open Scope string_scope.
Import ListNotations.
Definition observed_paths := (nested_paths ++ [WordPath Current ["first"]; WordPath Current ["second"]])%list.
Definition linked_function := "nested::write_twice".
Definition linked_site := "contract".
Definition args_view (a b : u32) (_ : phase) (path : list String.string) :=
  match path with
  | ["first"] => Integer.value a | ["second"] => Integer.value b | _ => 0%Z end.
Definition execution_claim (P Q : observations -> Prop) :=
  forall (initial : Outer.t) (a b : u32),
    P (memory_view initial initial (args_view a b)) ->
    exists final,
    {{ SimulateM.eval_f (run_twice root a b) [initial]%stack 🌲 (Output.Success tt, [final]%stack) }} /\
    Q (memory_view initial final (args_view a b)).
