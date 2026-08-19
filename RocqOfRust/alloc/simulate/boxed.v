Require Import simulate.RocqOfRust.
Require Import alloc.links.alloc.
Require Import alloc.links.boxed.

Module Impl_Box.
  Definition Self (T : Set) : Set :=
    Box.t T Global.t.

  Definition new {T : Set} (x : T) : Self T :=
    {| Box.value := x |}.

  Lemma new_eq {T : Set} `{Link T}
      (stack : Stack.t)
      (x : T) :
    {{
      SimulateM.eval_f
        (Impl_Box.run_new x)
        stack 🌲
      (
        Output.Success (new x),
        stack
      )
    }}.
  Proof.
  Admitted.
End Impl_Box.
