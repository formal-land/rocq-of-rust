Require Import RocqOfRust.RocqOfRust.
Require Import simulations.M.
Require Import core.simulations.default.
Require Import core.simulations.eq.

Module ImplEq.
  Global Instance I (A E : Set) `{Eq.Trait A} `{Eq.Trait E} :
    Eq.Trait (Result.t A E) := {
      eqb x y := 
        match x with
        | Result.Ok a =>
          match y with
          | Result.Ok b => Eq.eqb a b
          | Result.Err _ => false
          end
        | Result.Err e1 =>
          match y with
          | Result.Ok _ => false
          | Result.Err e2 => Eq.eqb e1 e2
          end
        end;
    }.
End ImplEq.
