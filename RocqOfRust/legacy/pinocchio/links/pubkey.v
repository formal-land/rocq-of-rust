Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.links.array.
Require Import pinocchio.pubkey.
Require Import core.links.option.
Require Import core.links.result.
Require Import pinocchio.links.program_error.

Import pinocchio.pubkey.pubkey.

Module Pubkey.
  Definition t : Set :=
    array.t u8 {| Integer.value := 32 |}.

    Global Instance Link_Pubkey : Link Pubkey.t.
    Proof.
      unfold Pubkey.t.
      typeclasses eauto.
    Defined.
End Pubkey.

Instance run_log
      (pubkey : '& Pubkey.t) :
    Run.Trait
      log [] [] [φ pubkey]
      unit.
  Proof.
    constructor.
    run_symbolic.
    admit.
  Admitted.
  Global Opaque run_log.

Instance run_find_program_address
  (seeds : '& (list ('& (list (Integer.t IntegerKind.U8)))))
  (pubkey : '& Pubkey.t) :
Run.Trait
  find_program_address [] [] [φ seeds; φ pubkey]
  ('& Pubkey.t * u8).
Proof.
  constructor.
  run_symbolic.
  admit.
Admitted.
Global Opaque run_find_program_address.

Instance run_try_find_program_address
  (seeds : '& (list ('& (list (Integer.t IntegerKind.U8)))))
  (program_id : '& Pubkey.t) :
Run.Trait
  try_find_program_address [] [] [φ seeds; φ program_id]
  (option ('& Pubkey.t * u8)).
Proof.
  constructor.
  run_symbolic.
  admit.
Admitted.
Global Opaque run_try_find_program_address.

Instance run_create_program_address
  (seeds : '& (list ('& (list (Integer.t IntegerKind.U8)))))
  (program_id : '& Pubkey.t) :
  Run.Trait
    create_program_address [] [] [φ seeds; φ program_id]
    (Result.t ('& Pubkey.t) ProgramError.t).
Proof.
  constructor.
  run_symbolic.
  admit.
Admitted.
Global Opaque run_create_program_address.

Instance run_checked_create_program_address
  (seeds : '& (list ('& (list (Integer.t IntegerKind.U8)))))
  (program_id : '& Pubkey.t) :
  Run.Trait
    checked_create_program_address [] [] [φ seeds; φ program_id]
    (Result.t ('& Pubkey.t) ProgramError.t).
Proof.
  constructor.
  run_symbolic.
  admit.
Admitted.
Global Opaque run_checked_create_program_address.
