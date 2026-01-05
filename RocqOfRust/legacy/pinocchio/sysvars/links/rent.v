Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import pinocchio.links.account_info.
Require Import pinocchio.links.pubkey.
Require Import pinocchio.links.lib.
Require Import pinocchio.sysvars.rent.
Require Import core.links.clone.
Require Import core.links.marker.
Require Import core.links.result.
Require Import core.links.default.
Require Import pinocchio.links.program_error.

Instance run_RENT_ID :
  Run.Trait
    pinocchio.sysvars.rent.sysvars.rent.value_RENT_ID [] [] []
    (Ref.t Pointer.Kind.Raw Pubkey.t).
Proof.
  constructor. 
  run_symbolic.
  - admit.
  - admit.
Admitted.
Global Opaque run_RENT_ID.

Instance run_DEFAULT_LAMPORTS_PER_BYTE_YEAR :
  Run.Trait
    pinocchio.sysvars.rent.sysvars.rent.value_DEFAULT_LAMPORTS_PER_BYTE_YEAR [] [] []
    (Ref.t Pointer.Kind.Raw u64).
Proof.
  constructor. run_symbolic.
Defined.
Global Opaque run_DEFAULT_LAMPORTS_PER_BYTE_YEAR.

Instance run_DEFAULT_EXEMPTION_THRESHOLD :
  Run.Trait
    pinocchio.sysvars.rent.sysvars.rent.value_DEFAULT_EXEMPTION_THRESHOLD [] [] []
    (Ref.t Pointer.Kind.Raw F64.t).
Proof.
  constructor. admit.
Admitted.
Global Opaque run_DEFAULT_EXEMPTION_THRESHOLD.

Instance run_DEFAULT_EXEMPTION_THRESHOLD_AS_U64 :
  Run.Trait
    pinocchio.sysvars.rent.sysvars.rent.value_DEFAULT_EXEMPTION_THRESHOLD_AS_U64 [] [] []
    (Ref.t Pointer.Kind.Raw u64).
Proof.
  constructor. run_symbolic.
Defined.
Global Opaque run_DEFAULT_EXEMPTION_THRESHOLD_AS_U64.

Instance run_F64_EXEMPTION_THRESHOLD_AS_U64 :
  Run.Trait
    pinocchio.sysvars.rent.sysvars.rent.value_F64_EXEMPTION_THRESHOLD_AS_U64 [] [] []
    (Ref.t Pointer.Kind.Raw u64).
Proof.
  constructor. run_symbolic.
Defined.
Global Opaque run_F64_EXEMPTION_THRESHOLD_AS_U64.

Instance run_DEFAULT_BURN_PERCENT :
  Run.Trait
    pinocchio.sysvars.rent.sysvars.rent.value_DEFAULT_BURN_PERCENT [] [] []
    (Ref.t Pointer.Kind.Raw u8).
Proof.
  constructor. run_symbolic.
Defined.
Global Opaque run_DEFAULT_BURN_PERCENT.

Instance run_ACCOUNT_STORAGE_OVERHEAD :
  Run.Trait
    pinocchio.sysvars.rent.sysvars.rent.value_ACCOUNT_STORAGE_OVERHEAD [] [] []
    (Ref.t Pointer.Kind.Raw u64).
Proof.
  constructor. run_symbolic.
Defined.
Global Opaque run_ACCOUNT_STORAGE_OVERHEAD.

Module Rent.
  Record t : Set := {
    lamports_per_byte_year : u64;
    exemption_threshold : F64.t;
    burn_percent : u8
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "pinocchio::sysvars::rent::Rent";
    φ x :=
      Value.StructRecord "pinocchio::sysvars::rent::Rent" [] [] [
        ("lamports_per_byte_year", φ x.(lamports_per_byte_year));
        ("exemption_threshold", φ x.(exemption_threshold));
        ("burn_percent", φ x.(burn_percent))
      ];
  }.
End Rent.

Module RentDue.
  Inductive t : Set :=
  | Exempt
  | Paying (x : u64).

  Global Instance IsLink : Link t := {
    Φ := Ty.path "pinocchio::sysvars::rent::RentDue";
    φ v :=
      match v with
      | Exempt =>
          Value.StructTuple
            "pinocchio::sysvars::rent::RentDue::Exempt" [] [] []
      | Paying x =>
          Value.StructTuple
            "pinocchio::sysvars::rent::RentDue::Paying" [] [] [φ x]
      end;
  }.
End RentDue.


Module Impl_Rent.
  Definition Self : Set := Rent.t.

  Instance run_from_account_info
    (account_info : Ref.t Pointer.Kind.Ref AccountInfo.t) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_Rent.from_account_info
      [] []
      [φ account_info]
      (Result.t (Ref.t Pointer.Kind.Ref Self) ProgramError.t).
  Proof.
    constructor. admit.
  Admitted.
  Global Opaque run_from_account_info.

  Instance run_from_account_info_unchecked
    (account_info : Ref.t Pointer.Kind.Ref AccountInfo.t) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_Rent.from_account_info_unchecked
      [] []
      [φ account_info]
      (Result.t (Ref.t Pointer.Kind.Ref Self) ProgramError.t).
  Proof.
    constructor. admit.
  Admitted.
  Global Opaque run_from_account_info_unchecked.

  Instance run_from_bytes
    (bytes : Ref.t Pointer.Kind.Ref (list (Integer.t IntegerKind.U8))) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_Rent.from_bytes
      [] []
      [φ bytes]
      (Result.t (Ref.t Pointer.Kind.Ref Self) ProgramError.t).
  Proof.
    constructor. admit.
  Admitted.
  Global Opaque run_from_bytes.

  Instance run_from_bytes_unchecked
    (bytes : Ref.t Pointer.Kind.Ref (list (Integer.t IntegerKind.U8))) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_Rent.from_bytes_unchecked
      [] []
      [φ bytes]
      (Ref.t Pointer.Kind.Ref Self).
  Proof.
    constructor. admit.
  Admitted.
  Global Opaque run_from_bytes_unchecked.

  Instance run_calculate_burn
    (self : Ref.t Pointer.Kind.Ref Self)
    (rent_collected : u64) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_Rent.calculate_burn
      [] []
      [φ self; φ rent_collected]
      (u64 * u64)%type.
  Proof.
    constructor. admit.
  Admitted.
  Global Opaque run_calculate_burn.

  Instance run_due
    (self : Ref.t Pointer.Kind.Ref Self)
    (balance : u64)
    (data_len : usize)
    (years_elapsed : F64.t) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_Rent.due
      [] []
      [φ self; φ balance; φ data_len; φ years_elapsed]
      RentDue.t.
  Proof.
    constructor. admit.
  Admitted.
  Global Opaque run_due.

  Instance run_due_amount
    (self : Ref.t Pointer.Kind.Ref Self)
    (data_len : usize)
    (years_elapsed : F64.t) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_Rent.due_amount
      [] []
      [φ self; φ data_len; φ years_elapsed]
      u64.
  Proof.
    constructor. admit.
  Admitted.
  Global Opaque run_due_amount.

  Instance run_minimum_balance
    (self : Ref.t Pointer.Kind.Ref Self)
    (data_len : usize) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_Rent.minimum_balance
      [] []
      [φ self; φ data_len]
      u64.
  Proof.
    constructor. admit.
  Admitted.
  Global Opaque run_minimum_balance.

  Instance run_is_exempt
    (self : Ref.t Pointer.Kind.Ref Self)
    (lamports : u64)
    (data_len : usize) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_Rent.is_exempt
      [] []
      [φ self; φ lamports; φ data_len]
      bool.
  Proof.
    constructor. admit.
  Admitted.
  Global Opaque run_is_exempt.

  Instance run_is_default_rent_threshold
    (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_Rent.is_default_rent_threshold
      [] []
      [φ self]
      bool.
  Proof.
    constructor. admit.
  Admitted.
  Global Opaque run_is_default_rent_threshold.
End Impl_Rent.

Module Impl_RentDue.
  Definition Self : Set := RentDue.t.

  Instance run_lamports
    (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_RentDue.lamports
      [] []
      [φ self]
      u64.
  Proof.
    constructor. admit.
  Admitted.
  Global Opaque run_lamports.

  Instance run_is_exempt
    (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_RentDue.is_exempt
      [] []
      [φ self]
      bool.
  Proof.
    constructor. admit.
  Admitted.
  Global Opaque run_is_exempt.
End Impl_RentDue.

Module Impl_Default_for_Rent.
  Definition Self : Set := Rent.t.

  Definition run_default : Default.Run_default Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply pinocchio.sysvars.rent.sysvars.rent.Impl_core_default_Default_for_pinocchio_sysvars_rent_Rent.Implements. }
      { reflexivity. } }
    { constructor. admit. }
  Admitted.

  Instance run : Default.Run Self := { Default.default := run_default }.
End Impl_Default_for_Rent.

Module Impl_Clone_for_Rent.
  Definition Self : Set := Rent.t.

  Definition run_clone : Clone.Run_clone Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply pinocchio.sysvars.rent.sysvars.rent.Impl_core_clone_Clone_for_pinocchio_sysvars_rent_Rent.Implements. }
      { reflexivity. } }
    { constructor. admit. }
  Admitted.

  Instance run : Clone.Run Self := { Clone.clone := run_clone }.
End Impl_Clone_for_Rent.

Module Impl_Clone_for_RentDue.
  Definition Self : Set := RentDue.t.

  Definition run_clone : Clone.Run_clone Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply pinocchio.sysvars.rent.sysvars.rent.Impl_core_clone_Clone_for_pinocchio_sysvars_rent_RentDue.Implements. }
      { reflexivity. } }
    { constructor. admit. }
  Admitted.

  Instance run : Clone.Run Self := { Clone.clone := run_clone }.
End Impl_Clone_for_RentDue.

Module Impl_Copy_for_RentDue.
  Definition Self : Set := RentDue.t.
  Instance run : Copy.Run Self.
  Proof. 
    constructor.
    admit. 
  Admitted.
End Impl_Copy_for_RentDue.
