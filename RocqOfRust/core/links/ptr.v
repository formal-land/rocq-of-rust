Require Import links.RocqOfRust.

Require Import core.ptr.mod.
Import core.ptr.mod.ptr.

Definition run_write_volatile (T: Set) `{Link T} (dst: '&mut T) (src: T) :
    Run.Trait
        write_volatile [] [] [φ dst] unit.
Proof.
Admitted.
Global Opaque run_write_volatile.
