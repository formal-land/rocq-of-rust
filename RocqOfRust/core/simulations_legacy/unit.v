Require Import Stdlib.Strings.String.
Require Import RocqOfRust.simulations_legacy.M.
Require Import core.simulations_legacy.eq.

Module ImplEq.
  Global Instance I :
    Eq.Trait unit := {
      eqb _ _ := true;
    }.
End ImplEq.
