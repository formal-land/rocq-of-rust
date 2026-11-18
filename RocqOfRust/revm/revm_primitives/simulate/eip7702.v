From Stdlib Require Import ZArith.

Require Import links.M.

Open Scope Z_scope.

(** revm_primitives/eip7702.rs *)
Definition PER_AUTH_BASE_COST : u64 := {| Integer.value := 12500 |}.

Definition PER_EMPTY_ACCOUNT_COST : u64 := {| Integer.value := 25000 |}.
