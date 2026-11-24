Require Import RocqOfRust.RocqOfRust ReleaseTests.generic.
Definition array_identity (n x : Value.t) : M :=
  let* p := M.alloc (Ty.apply (Ty.path "array") [n] [Ty.path "u8"]) x in M.read p.
Example retains_type_and_const (T : Ty.t) (n x : Value.t) :
  symbolic [n] [T] [x] =
  array_identity (M.symbolic_const "generic::symbolic::{constant#0}" [n] [T]) x.
Proof. reflexivity. Qed.
Example retains_separate_owner (n x : Value.t) :
  plus_one [n] [] [x] =
  array_identity (M.symbolic_const "generic::plus_one::{constant#0}" [n] []) x.
Proof. reflexivity. Qed.
