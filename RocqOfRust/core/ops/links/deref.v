Require Import RocqOfRust.RocqOfRust.
Require Import links.M.

(*
pub trait Deref {
    type Target: ?Sized;
    fn deref(&self) -> &Self::Target;
}
*)
Module Deref.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::ops::deref::Deref";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_deref
      (Self : Set) `{Link Self}
      (Target : Set) `{Link Target}
      (deref : PolymorphicFunction.t) :
      Set := {
    deref_is_method :: IsTraitMethod.C (trait Self) "deref" deref;
    run_deref (self : '& Self) :: Run.Trait deref [] [] [ φ self ] ('& Target);
  }.

  Class Run
      (Self : Set) `{Link Self}
      (Target : Set) `{Link Target} :
      Set := {
    deref : PolymorphicFunction.t;
    method_deref :: Method_deref Self Target deref;
  }.
End Deref.
Export (hints) Deref.

(*
pub trait DerefMut: Deref {
    fn deref_mut(&mut self) -> &mut Self::Target;
}
*)
Module DerefMut.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::ops::deref::DerefMut";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_deref_mut
      (Self : Set) `{Link Self}
      (Target : Set) `{Link Target}
      (deref_mut : PolymorphicFunction.t) :
      Set := {
    deref_mut_is_method :: IsTraitMethod.C (trait Self) "deref_mut" deref_mut;
    run_deref_mut (self : '&mut Self) :: Run.Trait deref_mut [] [] [ φ self ] ('&mut Target);
  }.

  Class Run
      (Self : Set) `{Link Self}
      (Target : Set) `{Link Target} :
      Set := {
    deref_mut : PolymorphicFunction.t;
    method_deref_mut :: Method_deref_mut Self Target deref_mut;
  }.
End DerefMut.
Export (hints) DerefMut.
