Require Import RocqOfRust.RocqOfRust.
Require Import links.M.

Module Global.
  Parameter t : Set.

  Parameter to_value : t -> Value.t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "alloc::alloc::Global";
    φ := to_value;
  }.

  Global Instance IsOfTy : OfTy.C (Ty.path "alloc::alloc::Global") := {
    A := t;
    eq := eq_refl;
  }.
End Global.
