Require Import links.RocqOfRust.
Require Import core.links.option.
Require Import revm.revm_primitives.hardfork.

Module SpecId.
  RocqOfRustLinkEnum "revm_primitives::hardfork::SpecId" :=
  | FRONTIER
  | FRONTIER_THAWING
  | HOMESTEAD
  | DAO_FORK
  | TANGERINE
  | SPURIOUS_DRAGON
  | BYZANTIUM
  | CONSTANTINOPLE
  | PETERSBURG
  | ISTANBUL
  | MUIR_GLACIER
  | BERLIN
  | LONDON
  | ARROW_GLACIER
  | GRAY_GLACIER
  | MERGE
  | SHANGHAI
  | CANCUN
  | PRAGUE
  | OSAKA
  | AMSTERDAM
  .
  Definition get_discriminant (x : t) : Z :=
    match x with
    | FRONTIER => 0
    | FRONTIER_THAWING => 1
    | HOMESTEAD => 2
    | DAO_FORK => 3
    | TANGERINE => 4
    | SPURIOUS_DRAGON => 5
    | BYZANTIUM => 6
    | CONSTANTINOPLE => 7
    | PETERSBURG => 8
    | ISTANBUL => 9
    | MUIR_GLACIER => 10
    | BERLIN => 11
    | LONDON => 12
    | ARROW_GLACIER => 13
    | GRAY_GLACIER => 14
    | MERGE => 15
    | SHANGHAI => 16
    | CANCUN => 17
    | PRAGUE => 18
    | OSAKA => 19
    | AMSTERDAM => 20
    end.

  Lemma cast_integer_eq (kind : IntegerKind.t) (x : t) :
    M.cast (Φ (Integer.t kind)) (φ x) =
    Value.Integer kind (Integer.normalize_wrap kind (get_discriminant x)).
  Proof.
    destruct x;
      with_strategy transparent [φ] cbn;
      apply M.is_discriminant_tuple_eq;
      (
        apply hardfork.IsDiscriminant_SpecId_FRONTIER ||
        apply hardfork.IsDiscriminant_SpecId_FRONTIER_THAWING ||
        apply hardfork.IsDiscriminant_SpecId_HOMESTEAD ||
        apply hardfork.IsDiscriminant_SpecId_DAO_FORK ||
        apply hardfork.IsDiscriminant_SpecId_TANGERINE ||
        apply hardfork.IsDiscriminant_SpecId_SPURIOUS_DRAGON ||
        apply hardfork.IsDiscriminant_SpecId_BYZANTIUM ||
        apply hardfork.IsDiscriminant_SpecId_CONSTANTINOPLE ||
        apply hardfork.IsDiscriminant_SpecId_PETERSBURG ||
        apply hardfork.IsDiscriminant_SpecId_ISTANBUL ||
        apply hardfork.IsDiscriminant_SpecId_MUIR_GLACIER ||
        apply hardfork.IsDiscriminant_SpecId_BERLIN ||
        apply hardfork.IsDiscriminant_SpecId_LONDON ||
        apply hardfork.IsDiscriminant_SpecId_ARROW_GLACIER ||
        apply hardfork.IsDiscriminant_SpecId_GRAY_GLACIER ||
        apply hardfork.IsDiscriminant_SpecId_MERGE ||
        apply hardfork.IsDiscriminant_SpecId_SHANGHAI ||
        apply hardfork.IsDiscriminant_SpecId_CANCUN ||
        apply hardfork.IsDiscriminant_SpecId_PRAGUE ||
        apply hardfork.IsDiscriminant_SpecId_OSAKA ||
        apply hardfork.IsDiscriminant_SpecId_AMSTERDAM
      ).
  Qed.
End SpecId.
Export (hints) SpecId.

Module Impl_SpecId.
  Definition Self : Set := SpecId.t.

  Instance run_is_enabled_in (self other : Self) :
    Run.Trait
      hardfork.Impl_revm_primitives_hardfork_SpecId.is_enabled_in [] [] [ φ self; φ other ]
      bool.
  Proof.
    constructor.
    run_symbolic.
    change_cast_integer.
    eapply Run.Rewrite. {
      do 2 rewrite SpecId.cast_integer_eq.
      reflexivity.
    }
    run_symbolic.
  Defined.
  Global Opaque run_is_enabled_in.
End Impl_SpecId.
Export (hints) Impl_SpecId.
