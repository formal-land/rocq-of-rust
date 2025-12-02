Require Import RocqOfRust.RocqOfRust.
Require Import simulations.M.
Require Import core.simulations.eq.

Module ImplEq.
  Global Instance I (A B : Set) `{Eq.Trait A} `{Eq.Trait B} :
    Eq.Trait (A * B) := {
      eqb '(a, b) '(c, d) := ((a =? c) && (b =? d))%bool;
    }.
End ImplEq.
