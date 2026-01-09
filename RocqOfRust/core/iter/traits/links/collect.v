Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.iter.traits.collect.
Require Import core.iter.traits.links.iterator.

(*
pub trait IntoIterator {
    type Item;
    type IntoIter: Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter;
}
*)
Module IntoIterator.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::iter::traits::collect::IntoIterator";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Module Types.
    Record t : Type := {
      Item : Set;
      IntoIter : Set;
    }.

    Class AreLinks (types : t) : Set := {
      H_Item : Link types.(Item);
      H_IntoIter : Link types.(IntoIter);
    }.

    Instance IsLinkItem (types : t) (H : AreLinks types) : Link types.(Item) :=
      H.(H_Item _).
    Instance IsLinkIntoIter (types : t) (H : AreLinks types) : Link types.(IntoIter) :=
      H.(H_IntoIter _).
  End Types.
  Export (hints) Types.

  Class Method_into_iter
      (Self : Set) `{Link Self}
      (types : Types.t) `{Types.AreLinks types} :
      Set := {
    into_iter : PolymorphicFunction.t;
    into_iter_is_method :: IsTraitMethod.C (trait Self) "into_iter" into_iter;
    run_into_iter (self : Self) :: Run.Trait into_iter [] [] [φ self] types.(Types.IntoIter);
  }.

  Class Run
      (Self : Set) `{Link Self}
      (types : Types.t) `{Types.AreLinks types} :
      Set := {
    Item_IsAssociated :
      IsTraitAssociatedType
        "core::iter::traits::collect::IntoIterator" [] [] (Φ Self)
        "Item" (Φ types.(Types.Item));
    IntoIter_IsAssociated :
      IsTraitAssociatedType
        "core::iter::traits::collect::IntoIterator" [] [] (Φ Self)
        "IntoIter" (Φ types.(Types.IntoIter));
    run_Iterator_for_IntoIter :: Iterator.Run types.(Types.IntoIter) types.(Types.Item);
    method_into_iter :: Method_into_iter Self types;
  }.
End IntoIterator.
Export (hints) IntoIterator.

(* impl<I: Iterator> IntoIterator for I *)
Module Impl_IntoIterator_for_Iterator_I.
  Definition Self (I : Set) `{Link I} : Set :=
    I.

  (*
    type Item = I::Item;
    type IntoIter = I;
  *)
  Definition types
    (I : Set) `{Link I}
    (Item : Set) `{Link Item} :
    IntoIterator.Types.t :=
  {|
    IntoIterator.Types.Item := Item;
    IntoIterator.Types.IntoIter := Self I;
  |}.

  Instance types_AreLinks
    (I : Set) `{Link I}
    (Item : Set) `{Link Item} :
    IntoIterator.Types.AreLinks (types I Item).
  Proof.
    now constructor.
  Defined.

  Instance method_into_iter
    (I : Set) `{Link I}
    (Item : Set) `{Link Item} :
    IntoIterator.Method_into_iter (Self I) (types I Item).
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply iter.traits.collect.Impl_core_iter_traits_collect_IntoIterator_where_core_iter_traits_iterator_Iterator_I_for_I.Implements. }
      { reflexivity. }
    }
    { constructor.
      run_symbolic.
    }
  Defined.

  Instance run
    (I : Set) `{Link I}
    (Item : Set) `{Link Item}
    `{!Iterator.Run I Item} :
    IntoIterator.Run (Self I) (types I Item).
  Proof.
  Admitted.
End Impl_IntoIterator_for_Iterator_I.
Export (hints) Impl_IntoIterator_for_Iterator_I.
