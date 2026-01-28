Require Import links.RocqOfRust.
Require Import core.borrow.

(*
pub trait Borrow<Borrowed>
where
    Borrowed: ?Sized,
{
    // Required method
    fn borrow(&self) -> &Borrowed;
}
*)
Module Borrow.
  Definition trait (Self Borrowed : Set) `{Link Self} `{Link Borrowed} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::borrow::Borrow";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [ Φ Borrowed ];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_borrow (Self Borrowed : Set) `{Link Self} `{Link Borrowed} : Set := {
    borrow : PolymorphicFunction.t;
    borrow_is_method :: IsTraitMethod.C (trait Self Borrowed) "borrow" borrow;
    run_borrow (self : '& Self) :: Run.Trait borrow [] [] [ φ self ] ('& Borrowed);
  }.

  Class Run (Self Borrowed : Set) `{Link Self} `{Link Borrowed} : Set := {
    method_borrow :: Method_borrow Self Borrowed;
  }.
End Borrow.
Export (hints) Borrow.

(* impl<T: ?Sized> Borrow<T> for T *)
Module Impl_Borrow_T_for_T.
  Definition Self (T : Set): Set :=
    T.

  Instance run (T : Set) `{Link T} : Borrow.Run (Self T) T.
  Admitted.
End Impl_Borrow_T_for_T.
Export (hints) Impl_Borrow_T_for_T.

(*
pub trait BorrowMut<Borrowed: ?Sized>: Borrow<Borrowed> {
    fn borrow_mut(&mut self) -> &mut Borrowed;
}
*)
Module BorrowMut.
  Definition trait (Self Borrowed : Set) `{Link Self} `{Link Borrowed} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::borrow::BorrowMut";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [ Φ Borrowed ];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_borrow_mut (Self Borrowed : Set) `{Link Self} `{Link Borrowed} : Set := {
    borrow_mut : PolymorphicFunction.t;
    borrow_mut_is_method :: IsTraitMethod.C (trait Self Borrowed) "borrow_mut" borrow_mut;
    run_borrow_mut (self : '&mut Self) :: Run.Trait borrow_mut [] [] [ φ self ] ('&mut Borrowed);
  }.

  Class Run (Self Borrowed : Set) `{Link Self} `{Link Borrowed} : Set := {
    run_Borrow_for_Self : Borrow.Run Self Borrowed;
    method_borrow_mut :: Method_borrow_mut Self Borrowed;
  }.
End BorrowMut.
Export (hints) BorrowMut.
