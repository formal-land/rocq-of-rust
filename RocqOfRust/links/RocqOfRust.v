(** This file re-exports both the main RocqOfRust definitions and the links module,
    so that links files can use a single import. *)

Declare ML Module "rocqofrust_link_plugin".

Require Export RocqOfRust.RocqOfRust.
Require Export RocqOfRust.links.M.

(* There is no export mode available at the moment. *)
Global Opaque Z.add Z.sub Z.mul Z.div Z.modulo Z.pow.
