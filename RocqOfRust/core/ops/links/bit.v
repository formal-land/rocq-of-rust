Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.ops.bit.

(*
pub trait BitAnd<Rhs = Self> {
    type Output;

    fn bitand(self, rhs: Rhs) -> Self::Output;
}
*)
Module BitAnd.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::ops::bit::BitAnd";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [ Φ Rhs ];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_bitand (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    bitand : PolymorphicFunction.t;
    bitand_is_method :: IsTraitMethod.C (trait Self Rhs) "bitand" bitand;
    run_bitand (self : Self) (rhs : Rhs) :: Run.Trait bitand [] [] [ φ self; φ rhs ] Output;
  }.

  Class Run (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    method_bitand :: Method_bitand Self Rhs Output;
  }.
End BitAnd.
Export (hints) BitAnd.

(*
pub trait BitOr<Rhs = Self> {
    type Output;

    fn bitor(self, rhs: Rhs) -> Self::Output;
}
*)
Module BitOr.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::ops::bit::BitOr";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [ Φ Rhs ];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_bitor (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    bitor : PolymorphicFunction.t;
    bitor_is_method :: IsTraitMethod.C (trait Self Rhs) "bitor" bitor;
    run_bitor (self : Self) (rhs : Rhs) :: Run.Trait bitor [] [] [ φ self; φ rhs ] Output;
  }.

  Class Run (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    method_bitor :: Method_bitor Self Rhs Output;
  }.
End BitOr.
Export (hints) BitOr.


(*
pub trait BitXor<Rhs = Self> {
    type Output;

    fn bitxor(self, rhs: Rhs) -> Self::Output;
}
*)
Module BitXor.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::ops::bit::BitXor";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [ Φ Rhs ];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_bitxor (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    bitxor : PolymorphicFunction.t;
    bitxor_is_method :: IsTraitMethod.C (trait Self Rhs) "bitxor" bitxor;
    run_bitxor (self : Self) (rhs : Rhs) :: Run.Trait bitxor [] [] [ φ self; φ rhs ] Output;
  }.

  Class Run (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    method_bitxor :: Method_bitxor Self Rhs Output;
  }.
End BitXor.
Export (hints) BitXor.

(*
pub trait Shl<Rhs = Self> {
    type Output;

    fn shl(self, rhs: Rhs) -> Self::Output;
}
*)
Module Shl.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::ops::bit::Shl";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [ Φ Rhs ];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_shl (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    shl : PolymorphicFunction.t;
    shl_is_method :: IsTraitMethod.C (trait Self Rhs) "shl" shl;
    run_shl (self : Self) (rhs : Rhs) :: Run.Trait shl [] [] [ φ self; φ rhs ] Output;
  }.

  Class Run (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    method_shl :: Method_shl Self Rhs Output;
  }.
End Shl.
Export (hints) Shl.

(*
pub trait Shr<Rhs = Self> {
    type Output;

    fn shr(self, rhs: Rhs) -> Self::Output;
}
*)
Module Shr.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::ops::bit::Shr";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [ Φ Rhs ];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_shr (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    shr : PolymorphicFunction.t;
    shr_is_method :: IsTraitMethod.C (trait Self Rhs) "shr" shr;
    run_shr (self : Self) (rhs : Rhs) :: Run.Trait shr [] [] [ φ self; φ rhs ] Output;
  }.

  Class Run (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    method_shr :: Method_shr Self Rhs Output;
  }.
End Shr.
Export (hints) Shr.

(*
pub trait Not {
    type Output;

    fn not(self) -> Self::Output;
}
*)
Module Not.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::ops::bit::Not";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_not (Self Output : Set) `{Link Self} `{Link Output} : Set := {
    not : PolymorphicFunction.t;
    not_is_method :: IsTraitMethod.C (trait Self) "not" not;
    run_not (self : Self) :: Run.Trait not [] [] [ φ self ] Output;
  }.

  Class Run (Self Output : Set) `{Link Self} `{Link Output} : Set := {
    method_not :: Method_not Self Output;
  }.
End Not.
Export (hints) Not.
