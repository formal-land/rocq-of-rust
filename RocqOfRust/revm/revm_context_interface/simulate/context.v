Require Import simulate.RocqOfRust.
From Stdlib Require Import String.

Module ContextError.
  Inductive t (DbError : Set) : Set :=
  | Db (error : DbError)
  | Custom (message : string).

  Arguments Db {DbError}.

  Arguments Custom {DbError}.
End ContextError.
