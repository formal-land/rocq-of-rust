Require Import links.RocqOfRust.

Module String.
  Parameter t : Set.

  Parameter to_value : t -> Value.t.

  Instance IsLink : Link t := {
    Φ := Ty.path "alloc::alloc::String";
    φ := to_value;
  }.
End String.
Export (hints) String.
