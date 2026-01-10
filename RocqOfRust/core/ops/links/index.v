Require Import RocqOfRust.RocqOfRust.
Require Import links.M.
Require Import core.links.array.
(*
  pub trait Index<Idx: ?Sized> {
    type Output: ?Sized;

    fn index(&self, index: Idx) -> &Self::Output;
  }
*)
Module Index.
  Definition trait (Self Idx : Set) `{Link Self} `{Link Idx} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::ops::index::Index";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [Φ Idx];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_index
      (Self Idx Output : Set) `{Link Self} `{Link Idx} `{Link Output} :
      Set := {
    index : PolymorphicFunction.t;
    index_is_method :: IsTraitMethod.C (trait Self Idx) "index" index;
    run_index (self : '& Self) (idx : Idx) ::
      Run.Trait index [] [] [ φ self; φ idx ] ('& Output);
  }.

  Class Run
      (Self : Set) `{Link Self}
      (Idx : Set) `{Link Idx}
      (Output : Set) `{Link Output} :
    Set := {
      Output_IsAssociated :
      IsTraitAssociatedType
        "core::slice::index::SliceIndex" [] [Φ Idx] (Φ Self)
        "Output" (Φ Output);
      method_index :: Method_index Self Idx Output;
  }.
End Index.
Export (hints) Index.

(*
impl<T, I, const N: usize> Index<I> for [T; N]
where
    [T]: Index<I>,
*)
Module Impl_Index_for_Array.
  Definition Self (T I : Set) (N : usize) : Set :=
    array.t T N.

  (* type Output = <[T] as Index<I>>::Output; *)
  Definition Output (T I : Set) (N : usize) (Index_Output : Set)
      `{Link T} `{Link I} `{Link Index_Output}
      `{!Index.Run T I Index_Output} :
      Set :=
    Index_Output.

  Instance run (T I : Set) (N : usize) {Index_Output : Set}
      `{Link T} `{Link I} `{Link Index_Output}
      `{!Index.Run T I Index_Output} :
    Index.Run (Self T I N) I (Output T I N Index_Output).
  Admitted.
End Impl_Index_for_Array.
Export (hints) Impl_Index_for_Array.

(*
pub trait IndexMut<Idx>: Index<Idx>
where
    Idx: ?Sized,
{
    // Required method
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output;
}
*)
Module IndexMut.
  Definition trait (Self Idx : Set) `{Link Self} `{Link Idx} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::ops::index::IndexMut";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [Φ Idx];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_index_mut
      (Self Idx Output : Set) `{Link Self} `{Link Idx} `{Link Output} :
      Set := {
    index_mut : PolymorphicFunction.t;
    index_mut_is_method :: IsTraitMethod.C (trait Self Idx) "index_mut" index_mut;
    run_index_mut (self : '&mut Self) (index : Idx) ::
      Run.Trait index_mut [] [] [ φ self; φ index ] ('&mut Output);
  }.

  Class Run
    (Self : Set) `{Link Self}
    (Idx : Set) `{Link Idx}
    (Output : Set) `{Link Output} :
    Set := {
      run_Index_for_Self : Index.Run Self Idx Output;
      method_index_mut :: Method_index_mut Self Idx Output;
    }.
End IndexMut.
Export (hints) IndexMut.
