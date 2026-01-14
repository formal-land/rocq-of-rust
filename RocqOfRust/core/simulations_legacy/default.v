Require Import RocqOfRust.RocqOfRust.

(*
    pub trait Default: Sized {
        // Required method
        fn default() -> Self;
    }
*)
Module Default.
  Class Trait (Self : Set) : Set := {
    default : Self;
  }.
End Default.
