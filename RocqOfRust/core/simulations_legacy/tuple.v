Require Import RocqOfRust.RocqOfRust.
Require Import simulations_legacy.M.
Require Import core.simulations_legacy.eq.

Module ImplEq.
  Global Instance I (A B : Set) `{Eq.Trait A} `{Eq.Trait B} :
    Eq.Trait (A * B) := {
      eqb '(a, b) '(c, d) := ((a =? c) && (b =? d))%bool;
    }.
End ImplEq.
