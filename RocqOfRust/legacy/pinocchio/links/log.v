Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.ops.links.deref.
Require Import pinocchio.log.
Require Import pinocchio.links.account_info.
Require Import pinocchio.links.pubkey.

Instance run_sol_log
  (message : '& (list (Integer.t IntegerKind.U8))) :
  Run.Trait
    log.sol_log
    [] []
    [φ message]
    unit.
Proof.
  constructor.
  admit.
Admitted.
Global Opaque run_sol_log.

Instance run_sol_log_64
  (arg1 arg2 arg3 arg4 arg5 : u64) :
  Run.Trait
    log.sol_log_64
    [] []
    [φ arg1; φ arg2; φ arg3; φ arg4; φ arg5]
    unit.
Proof.
  constructor.
  admit.
Admitted.
Global Opaque run_sol_log_64.

Instance run_sol_log_data
  (data : '& (list (list (Integer.t IntegerKind.U8)))) :
  Run.Trait
    log.sol_log_data
    [] []
    [φ data]
    unit.
Proof.
  constructor.
  admit.
Admitted.
Global Opaque run_sol_log_data.

Instance run_sol_log_slice
  (slice : '& (list (Integer.t IntegerKind.U8))) :
  Run.Trait
    log.sol_log_slice
    [] []
    [φ slice]
    unit.
Proof.
  constructor.
  admit.
Admitted.
Global Opaque run_sol_log_slice.

Instance run_sol_log_params
  (accounts : '& (list AccountInfo.t))
  (data : '& (list (Integer.t IntegerKind.U8))) :
  Run.Trait
    log.sol_log_params
    [] []
    [φ accounts; φ data]
    unit.
Proof.
  constructor.
  admit.
Admitted.
Global Opaque run_sol_log_params.

Instance run_sol_log_compute_units :
  Run.Trait
    log.sol_log_compute_units
    [] [] []
    unit.
Proof.
  constructor.
  admit.
Admitted.
Global Opaque run_sol_log_compute_units.
