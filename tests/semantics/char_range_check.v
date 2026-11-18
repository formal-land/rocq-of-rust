Require Import RocqOfRust.evaluate.RocqOfRust ReleaseTests.char_range.
Instance run_classify (c : Char.t) : Run.Trait classify [] [] [φ c] u8.
Proof. constructor. run_symbolic. Defined.

Example scalar_boundaries :
  List.map (fun c => Evaluate.eval_f 120 (run_classify (Char.Make c)) []%stack)
    [945;947;948;121;122;128570;32] =
  List.map (fun z => Execution.Done (Output.Success ({|Integer.value := z|} : u8), []%stack))
    [1;1;0;2;0;3;0].
Proof. vm_compute. reflexivity. Qed.
