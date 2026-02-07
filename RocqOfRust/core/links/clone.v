Require Import links.RocqOfRust.
Require Import core.clone.

(*
    pub trait Clone: Sized {
        fn clone(&self) -> Self;
        fn clone_from(&mut self, source: &Self)
    }
*)
Module Clone.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::clone::Clone";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_clone (Self : Set) `{Link Self} : Set := {
    clone : PolymorphicFunction.t;
    clone_is_method :: IsTraitMethod.C (trait Self) "clone" clone;
    run_clone (self : '& Self) :: Run.Trait clone [] [] [ φ self ] Self;
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    method_clone :: Method_clone Self;
    (* TODO: add [clone_from] *)
  }.
End Clone.
Export (hints) Clone.

Module Impl_Clone_for_bool.
  Definition Self : Set :=
    bool.

  Instance run_clone (self : '& bool) :
    Run.Trait clone.clone.impls.Impl_core_clone_Clone_for_bool.clone
      [] [] [ φ self ]
      bool.
  Proof.
    constructor.
    run_symbolic.
  Defined.
  Global Opaque run_clone.

  Instance method_clone : Clone.Method_clone bool.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply clone.impls.Impl_core_clone_Clone_for_bool.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run : Clone.Run bool := {}.
End Impl_Clone_for_bool.
Export (hints) Impl_Clone_for_bool.
