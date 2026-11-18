Require Import simulate.RocqOfRust.
From Stdlib Require Import List String.

Import ListNotations.

Module LocalContext.
  (** The shared buffer is threaded through calls instead of Rc<RefCell<_>>.
      Vector capacity has no observable effect in the executable model. *)
  Record t : Set := {
    shared_memory_buffer : list u8;
    precompile_error_message : option string;
  }.
End LocalContext.

Module Impl_LocalContext.
  Definition new : LocalContext.t := {|
    LocalContext.shared_memory_buffer := [];
    LocalContext.precompile_error_message := None;
  |}.

  Definition clear (self : LocalContext.t) : LocalContext.t := new.

  Definition set_precompile_error_context (self : LocalContext.t) (output : string) : LocalContext.t :=
    self <| LocalContext.precompile_error_message := Some output |>.

  Definition take_precompile_error_context (self : LocalContext.t) : option string * LocalContext.t :=
    (self.(LocalContext.precompile_error_message), self <| LocalContext.precompile_error_message := None |>).
End Impl_LocalContext.
