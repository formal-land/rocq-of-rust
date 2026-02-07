Require Import simulate.RocqOfRust.
Require Import alloc.links.alloc.
Require Import alloc.links.raw_vec.
Require Import alloc.links.slice.
Require Import alloc.vec.links.mod.

Module Impl_Slice.
  Definition Self (T : Set) : Set :=
    list T.

  Definition to_vec {T : Set} (self : Self T) : Vec.t T Global.t :=
    {|
      Vec.buf := {| RawVec.value := self |};
      Vec.len := {| Integer.value := Z.of_nat (List.length self) |};
    |}.

  Lemma to_vec_eq {T : Set} `{Link T}
      (stack : Stack.t)
      (ref_self : '& (Self T))
      (self : Self T) :
    CanRead.t stack self ref_self ->
    {{
      SimulateM.eval_f
        (Impl_Slice.run_to_vec ref_self)
        stack 🌲
      (
        Output.Success (to_vec self),
        stack
      )
    }}.
  Admitted.
End Impl_Slice.
