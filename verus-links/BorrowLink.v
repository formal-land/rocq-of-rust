Require Export RocqOfRust.simulate.RocqOfRust NestedSupport Assertion.
Import ListNotations.
Open Scope string_scope.
Import ListNotations.
Definition observed_paths := (nested_paths ++ [WordPath Current ["r"]; WordPath Expiry ["r"]])%list.
Definition linked_function := "nested::left_mut".
Definition linked_site := "contract".
Definition ret_view (v later : u32) (p : phase) (path : list String.string) :=
  match path with
  | ["r"] => Integer.value (match p with Expiry => later | _ => v end)
  | _ => 0%Z end.
Definition execution_claim (P Q : observations -> Prop) :=
  forall (initial : Outer.t),
    P (memory_view initial initial (fun _ _ => 0%Z)) ->
    {{ SimulateM.eval_f (run_left root) [initial]%stack 🌲
        (Output.Success left_ref, [initial]%stack) }} /\
    forall later : u32, exists inner returned updated final,
    Outer.SubPointer.get_pair.(SubPointer.Runner.projection) initial = Some inner /\
    Pair.SubPointer.get_left.(SubPointer.Runner.projection) inner = Some returned /\
    Pair.SubPointer.get_left.(SubPointer.Runner.injection) inner later = Some updated /\
    Outer.SubPointer.get_pair.(SubPointer.Runner.injection) initial updated = Some final /\
    Q (memory_view initial final (ret_view returned later)).
