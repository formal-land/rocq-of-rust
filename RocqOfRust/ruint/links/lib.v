Require Import links.RocqOfRust.
Require Import core.links.array.
Require Import core.links.cmp.
Require Import ruint.lib.

Module Uint.
  Record t {BITS LIMBS : usize} : Set := {
    value : Z;
  }.
  Arguments t : clear implicits.

  Parameter to_value : forall {BITS LIMBS : usize}, t BITS LIMBS -> Value.t.

  Instance IsLink {BITS LIMBS : usize} : Link (t BITS LIMBS) := {
    Φ := Ty.apply (Ty.path "ruint::Uint") [ φ BITS; φ LIMBS ] [];
    φ := to_value;
  }.

  Definition of_ty (BITS' LIMBS' : Value.t) (BITS LIMBS : usize) :
    BITS' = φ BITS ->
    LIMBS' = φ LIMBS ->
    OfTy.t (Ty.apply (Ty.path "ruint::Uint") [ BITS' ; LIMBS' ] []).
  Proof. intros. eapply OfTy.Make with (A := t BITS LIMBS). now subst. Defined.
  Smpl Add eapply of_ty : of_ty.
End Uint.
Export (hints) Uint.

Module Impl_PartialEq_for_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  Instance run (BITS LIMBS : usize) :
    PartialEq.Run (Self BITS LIMBS) (Uint.t BITS LIMBS).
  Admitted.
End Impl_PartialEq_for_Uint.
Export (hints) Impl_PartialEq_for_Uint.

Module Impl_Ord_for_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  Instance run (BITS LIMBS : usize) : Ord.Run (Self BITS LIMBS).
  Admitted.
End Impl_Ord_for_Uint.
Export (hints) Impl_Ord_for_Uint.

Module Impl_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  (* pub const fn from_limbs(limbs: [u64; LIMBS]) -> Self *)
  Instance run_from_limbs (BITS LIMBS : usize) (limbs : array.t u64 LIMBS) :
    Run.Trait
      (Impl_ruint_Uint_BITS_LIMBS.from_limbs (φ BITS) (φ LIMBS)) [] [] [ φ limbs ]
      (Self BITS LIMBS).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_from_limbs.

  (* pub const MASK: u64 = mask(BITS); *)
  Instance run_MASK (BITS LIMBS : usize) :
    Run.Trait
      (Impl_ruint_Uint_BITS_LIMBS.value_MASK (φ BITS) (φ LIMBS)) [] [] []
      ('* u64).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_MASK.

  (* pub const BITS: usize *)
  Instance run_BITS (BITS LIMBS : usize) :
    Run.Trait
      (Impl_ruint_Uint_BITS_LIMBS.value_BITS (φ BITS) (φ LIMBS)) [] [] []
      ('* usize).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_BITS.

  (* pub const ZERO: Self *)
  Instance run_ZERO (BITS LIMBS : usize) :
    Run.Trait
      (Impl_ruint_Uint_BITS_LIMBS.value_ZERO (φ BITS) (φ LIMBS)) [] [] []
      ('* (Self BITS LIMBS)).
  Proof.
    constructor.
    run_symbolic.
    constructor.
    eapply Run.Rewrite. {
      change (Value.Integer IntegerKind.U64 0) with (φ (A := u64) {| Integer.value := 0 |}).
      rewrite array.repeat_nat_φ_eq.
      reflexivity.
    }
    apply Run.run_f.
  Defined.
  Global Opaque run_ZERO.

  (* pub const MIN: Self *)
  Instance run_MIN (BITS LIMBS : usize) :
    Run.Trait
      (Impl_ruint_Uint_BITS_LIMBS.value_MIN (φ BITS) (φ LIMBS)) [] [] []
      ('* (Self BITS LIMBS)).
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_MIN.

  (* pub const MAX: Self *)
  Instance run_MAX (BITS LIMBS : usize) :
    Run.Trait
      (Impl_ruint_Uint_BITS_LIMBS.value_MAX (φ BITS) (φ LIMBS)) [] [] []
      ('* (Self BITS LIMBS)).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_MAX.

  (* pub const fn as_limbs(&self) -> &[u64; LIMBS] *)
  Instance run_as_limbs
    (BITS LIMBS : usize)
    (self : '& (Uint.t BITS LIMBS)) :
    Run.Trait
      (Impl_ruint_Uint_BITS_LIMBS.as_limbs (φ BITS) (φ LIMBS)) [] [] [ φ self ]
      ('& (array.t u64 LIMBS)).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_as_limbs.

  (* pub unsafe fn as_limbs_mut(&mut self) -> &mut [u64; LIMBS] *)
  Instance run_as_limbs_mut
    (BITS LIMBS : usize)
    (self : '&mut (Uint.t BITS LIMBS)) :
    Run.Trait
      (Impl_ruint_Uint_BITS_LIMBS.as_limbs_mut (φ BITS) (φ LIMBS)) [] [] [ φ self ]
      ('&mut (array.t u64 LIMBS)).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_as_limbs_mut.
End Impl_Uint.
Export (hints) Impl_Uint.
