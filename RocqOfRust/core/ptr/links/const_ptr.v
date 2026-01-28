Require Import links.RocqOfRust.
Require Import core.ptr.const_ptr.

Module Impl_pointer_const_T.
  Definition Self (T : Set) `{Link T} : Set := '*const T.

  (* pub const unsafe fn add(self, count: usize) -> Self *)
  Instance run_add
      (T : Set) `{Link T}
      (self : Self T)
      (count : usize) :
    Run.Trait (ptr.const_ptr.Impl_pointer_const_T.add (Φ T)) [] [] [ φ self; φ count ] (Self T).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_add.
End Impl_pointer_const_T.
Export (hints) Impl_pointer_const_T.
