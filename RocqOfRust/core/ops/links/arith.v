Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.ops.arith.

(*
pub trait Add<Rhs = Self> {
    type Output;

    fn add(self, rhs: Rhs) -> Self::Output;
}
*)
Module Add.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::ops::arith::Add";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [ Φ Rhs ];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_add (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    add : PolymorphicFunction.t;
    add_is_method :: IsTraitMethod.C (trait Self Rhs) "add" add;
    run_add (self : Self) (rhs : Rhs) :: Run.Trait add [] [] [ φ self; φ rhs ] Output;
  }.

  Class Run (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    method_add :: Method_add Self Rhs Output;
  }.
End Add.
Export (hints) Add.

(*
pub trait Sub<Rhs = Self> {
    type Output;

    fn sub(self, rhs: Rhs) -> Self::Output;
}
*)
Module Sub.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::ops::arith::Sub";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [ Φ Rhs ];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_sub (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    sub : PolymorphicFunction.t;
    sub_is_method :: IsTraitMethod.C (trait Self Rhs) "sub" sub;
    run_sub (self : Self) (rhs : Rhs) :: Run.Trait sub [] [] [ φ self; φ rhs ] Output;
  }.

  Class Run (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    method_sub :: Method_sub Self Rhs Output;
  }.
End Sub.
Export (hints) Sub.

(*
pub trait Mul<Rhs = Self> {
    type Output;

    // Required method
    fn mul(self, rhs: Rhs) -> Self::Output;
}
*)
Module Mul.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::ops::arith::Mul";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [ Φ Rhs ];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_mul (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    mul : PolymorphicFunction.t;
    mul_is_method :: IsTraitMethod.C (trait Self Rhs) "mul" mul;
    run_mul (self : Self) (rhs : Rhs) :: Run.Trait mul [] [] [ φ self; φ rhs ] Output;
  }.

  Class Run (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    method_mul :: Method_mul Self Rhs Output;
  }.
End Mul.
Export (hints) Mul.

(*
pub trait Div<Rhs = Self> {
    type Output;

    // Required method
    fn div(self, rhs: Rhs) -> Self::Output;
}
*)
Module Div.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::ops::arith::Div";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [ Φ Rhs ];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_div (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    div : PolymorphicFunction.t;
    div_is_method :: IsTraitMethod.C (trait Self Rhs) "div" div;
    run_div (self : Self) (rhs : Rhs) :: Run.Trait div [] [] [ φ self; φ rhs ] Output;
  }.

  Class Run (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    method_div :: Method_div Self Rhs Output;
  }.
End Div.
Export (hints) Div.

(*
pub trait Rem<Rhs = Self> {
    type Output;

    fn rem(self, rhs: Rhs) -> Self::Output;
}
*)
Module Rem.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::ops::arith::Rem";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [ Φ Rhs ];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_rem (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    rem : PolymorphicFunction.t;
    rem_is_method :: IsTraitMethod.C (trait Self Rhs) "rem" rem;
    run_rem (self : Self) (rhs : Rhs) :: Run.Trait rem [] [] [ φ self; φ rhs ] Output;
  }.

  Class Run (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    method_rem :: Method_rem Self Rhs Output;
  }.
End Rem.
Export (hints) Rem.
