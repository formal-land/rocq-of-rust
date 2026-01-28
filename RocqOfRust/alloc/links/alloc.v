Require Import links.RocqOfRust.

Module Global.
  Parameter t : Set.

  Parameter to_value : t -> Value.t.

  Instance IsLink : Link t := {
    Φ := Ty.path "alloc::alloc::Global";
    φ := to_value;
  }.

  Instance IsOfTy : OfTy.C (Ty.path "alloc::alloc::Global") := {
    A := t;
    eq := eq_refl;
  }.
End Global.
Export (hints) Global.
