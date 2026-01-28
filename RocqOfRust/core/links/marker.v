Require Import links.RocqOfRust.
Require Import core.links.clone.
Require Import core.marker.

(*
pub trait Copy: Clone {
    // Empty.
}
*)
Module Copy.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::marker::Copy";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Run (Self : Set) `{Link Self} : Set := {
    run_Clone_for_Self :: Clone.Run Self;
  }.
End Copy.
Export (hints) Copy.

(*
pub trait PointeeSized {
    // Empty.
}
*)
Module PointeeSized.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::marker::PointeeSized";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Run (Self : Set) `{Link Self} : Set := {
    dummy_empty_class : unit;
  }.
End PointeeSized.
Export (hints) PointeeSized.

(*
  pub struct PhantomData<T: PointeeSized>;
*)
Module PhantomData.
  Inductive t (T : Set) `{Link T} `{!PointeeSized.Run T} : Set := 
    | Make.

  Instance IsLink (T : Set) `{Link T} `{PointeeSized.Run T} : Link (t T) :=
    { Φ := Ty.apply (Ty.path "core::marker::PhantomData") [] [Φ T];
      φ _ := Value.StructTuple "core::marker::PhantomData" [] [Φ T] []
    }.

  Instance PointeeSized_Run_Ref {K A} `{Link A} `{PointeeSized.Run A}
    : PointeeSized.Run (Ref.t K A) :=
      { dummy_empty_class := tt }.
End PhantomData.
Export (hints) PhantomData.
