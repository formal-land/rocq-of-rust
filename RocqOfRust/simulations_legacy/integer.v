Require Import RocqOfRust.RocqOfRust.
Require Import links.M.
Require Import simulations_legacy.M.

Module U64.
  Definition checked_add (a b : Z) : option Z :=
    let sum := (a + b)%Z in
    if sum <? 2 ^ 64 then
      Some sum
    else
      None.
End U64.
