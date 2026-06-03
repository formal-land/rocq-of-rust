Require Import links.RocqOfRust.

Require Import core.ptr.mod.
Import core.ptr.mod.ptr.

Definition run_write_volatile (T: Set) `{Link T} (dst: '&mut T) (src: T) :
    Run.Trait
        write_volatile [] [] [φ dst] unit.
Proof.
Admitted.
Global Opaque run_write_volatile.

Instance run_ptr_copy_nonoverlapping {T : Set} `{Link T}
    (src : '*const T)
    (dst : '*mut T)
    (count : usize) :
  Run.Trait
    core.ptr.mod.ptr.copy_nonoverlapping [] [ Φ T ] [ φ src; φ dst; φ count ]
    unit.
Proof.
Admitted.
Global Opaque run_ptr_copy_nonoverlapping.
