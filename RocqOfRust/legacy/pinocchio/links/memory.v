Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import pinocchio.memory.
Require Import pinocchio.links.lib.

Instance run_sol_memcpy
  (dst : '& (list (Integer.t IntegerKind.U8)))
  (src : '& (list (Integer.t IntegerKind.U8)))
  (n : usize) :
  Run.Trait
    memory.sol_memcpy
    [] []
    [φ dst; φ src; φ n]
    unit.
Proof.
  constructor.
  admit.
Admitted.
Global Opaque run_sol_memcpy.

Instance run_copy_val
  (A : Set) `{Link A}
  (dst : '& A)
  (src : '& A) :
  Run.Trait
    memory.copy_val
    [] []
    [φ dst; φ src]
    unit.
Proof.
  constructor.
  admit.
Admitted.
Global Opaque run_copy_val.

Instance run_sol_memmove
  (dst : '* u8)
  (src : '* u8)
  (n : usize) :
  Run.Trait
    memory.sol_memmove
    [] []
    [φ dst; φ src; φ n]
    unit.
Proof.
  constructor.
  admit.
Admitted.
Global Opaque run_sol_memmove.

Instance run_sol_memcmp
  (s1 : '& (list (Integer.t IntegerKind.U8)))
  (s2 : '& (list (Integer.t IntegerKind.U8)))
  (n : usize) :
  Run.Trait
    memory.sol_memcmp
    [] []
    [φ s1; φ s2; φ n]
    i32.
Proof.
  constructor.
  admit.
Admitted.
Global Opaque run_sol_memcmp.

Instance run_sol_memset
  (s : '& (list (Integer.t IntegerKind.U8)))
  (c : u8)
  (n : usize) :
  Run.Trait
    memory.sol_memset
    [] []
    [φ s; φ c; φ n]
    unit.
Proof.
  constructor.
  admit.
Admitted.
Global Opaque run_sol_memset.
