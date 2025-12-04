Require Import Stdlib.Strings.String.
Require Import RocqOfRust.simulations.M.
Require Import core.simulations.eq.

Module ImplEq.
  Global Instance I :
    Eq.Trait unit := {
      eqb _ _ := true;
    }.
End ImplEq.
