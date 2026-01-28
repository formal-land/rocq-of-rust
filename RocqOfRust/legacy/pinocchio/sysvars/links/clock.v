Require Import links.RocqOfRust.
Require Import pinocchio.links.account_info.
Require Import pinocchio.links.pubkey.
Require Import pinocchio.links.lib.
Require Import pinocchio.sysvars.clock.
Require Import core.links.result.
Require Import pinocchio.links.program_error.

Instance run_CLOCK_ID :
  Run.Trait
    pinocchio.sysvars.clock.sysvars.clock.value_CLOCK_ID [] [] []
    ('* Pubkey.t).
Proof.
  constructor.
  admit.
Admitted.
Global Opaque run_CLOCK_ID.

Instance run_DEFAULT_TICKS_PER_SLOT :
  Run.Trait
    pinocchio.sysvars.clock.sysvars.clock.value_DEFAULT_TICKS_PER_SLOT [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_DEFAULT_TICKS_PER_SLOT.

Instance run_DEFAULT_TICKS_PER_SECOND :
  Run.Trait
    pinocchio.sysvars.clock.sysvars.clock.value_DEFAULT_TICKS_PER_SECOND [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_DEFAULT_TICKS_PER_SECOND.

Instance run_DEFAULT_MS_PER_SLOT :
  Run.Trait
    pinocchio.sysvars.clock.sysvars.clock.value_DEFAULT_MS_PER_SLOT [] [] []
    ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_DEFAULT_MS_PER_SLOT.

Module Clock.
  Record t : Set := {
    slot : u64;
    epoch_start_timestamp : i64;
    epoch : u64;
    leader_schedule_epoch : u64;
    unix_timestamp : i64
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "pinocchio::sysvars::clock::Clock";
    φ x :=
      Value.StructRecord "pinocchio::sysvars::clock::Clock" [] [] [
        ("slot", φ x.(slot));
        ("epoch_start_timestamp", φ x.(epoch_start_timestamp));
        ("epoch", φ x.(epoch));
        ("leader_schedule_epoch", φ x.(leader_schedule_epoch));
        ("unix_timestamp", φ x.(unix_timestamp))
      ];
  }.
End Clock.

Module Impl_Clock.
  Definition Self : Set := Clock.t.

  Instance run_LEN :
  Run.Trait
    pinocchio.sysvars.clock.sysvars.clock.Impl_pinocchio_sysvars_clock_Clock.value_LEN [] [] []
    ('* usize).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_LEN.

  Instance run_from_account_info
    (account_info : '& AccountInfo.t) :
    Run.Trait
      pinocchio.sysvars.clock.sysvars.clock.Impl_pinocchio_sysvars_clock_Clock.from_account_info
      [] []
      [φ account_info]
      (Result.t ('& Self) ProgramError.t).
  Proof.
    constructor.
    admit.
  Admitted.
  Global Opaque run_from_account_info.

  Instance run_from_account_info_unchecked
    (account_info : '& AccountInfo.t) :
    Run.Trait
      pinocchio.sysvars.clock.sysvars.clock.Impl_pinocchio_sysvars_clock_Clock.from_account_info_unchecked
      [] []
      [φ account_info]
      (Result.t ('& Self) ProgramError.t).
  Proof.
    constructor.
    admit.
  Admitted.
  Global Opaque run_from_account_info_unchecked.

  Instance run_from_bytes
    (bytes : '& (list (Integer.t IntegerKind.U8))) :
    Run.Trait
      pinocchio.sysvars.clock.sysvars.clock.Impl_pinocchio_sysvars_clock_Clock.from_bytes
      [] []
      [φ bytes]
      (Result.t ('& Self) ProgramError.t).
  Proof.
    constructor.
    admit.
  Admitted.
  Global Opaque run_from_bytes.

  Instance run_from_bytes_unchecked
    (bytes : '& (list (Integer.t IntegerKind.U8))) :
    Run.Trait
      pinocchio.sysvars.clock.sysvars.clock.Impl_pinocchio_sysvars_clock_Clock.from_bytes_unchecked
      [] []
      [φ bytes]
      ('& Self).
  Proof.
    constructor.
    admit.
  Admitted.
  Global Opaque run_from_bytes_unchecked.
End Impl_Clock.
