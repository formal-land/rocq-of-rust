Require Import RocqOfRust.evaluate.RocqOfRust RocqOfRust.core.char.methods.
Definition graphic := char.methods.Impl_char.is_ascii_graphic.
Instance run_graphic (c : '& Char.t) : Run.Trait graphic [] [] [φ c] bool.
Proof. constructor. unfold graphic. run_symbolic. Defined.
Example space_graphic :
  Evaluate.eval_f 100 (run_graphic (Ref.immediate Pointer.Kind.Ref (Char.Make 32))) []%stack =
  Execution.Done (Output.Success false, []%stack).
Proof. vm_compute. reflexivity. Qed.
