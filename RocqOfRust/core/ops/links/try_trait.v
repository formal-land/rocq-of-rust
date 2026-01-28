Require Import links.RocqOfRust.
Require Import core.ops.links.control_flow.
Require Import core.ops.try_trait.

(*
pub trait FromResidual<R = <Self as Try>::Residual> {
    fn from_residual(residual: R) -> Self;
}
*)
Module FromResidual.
  Definition trait (Self : Set) `{Link Self} (R : Set) `{Link R} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::ops::try_trait::FromResidual";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [Φ R];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_from_residual
      (Self : Set) `{Link Self}
      (R : Set) `{Link R} :
      Set := {
    from_residual : PolymorphicFunction.t;
    from_residual_is_method :: IsTraitMethod.C (trait Self R) "from_residual" from_residual;
    run_from_residual (residual : R) :: Run.Trait from_residual [] [] [ φ residual ] Self;
  }.

  Class Run (Self : Set) `{Link Self} (R : Set) `{Link R} : Set := {
    method_from_residual :: Method_from_residual Self R;
  }.
End FromResidual.
Export (hints) FromResidual.

(*
pub trait Try: FromResidual {
  type Output;
  type Residual;

  // Required methods
  fn from_output(output: Self::Output) -> Self;
  fn branch(self) -> ControlFlow<Self::Residual, Self::Output>;
}
*)
Module Try.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::ops::try_trait::Try";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Module Types.
    Record t : Type := {
      Output : Set;
      Residual : Set;
    }.

    Class AreLinks (types : t) : Set := {
      H_Output :: Link types.(Output);
      H_Residual :: Link types.(Residual);
    }.
  End Types.
  Export (hints) Types.

  Class Method_from_output
      (Self : Set) `{Link Self}
      (types : Types.t) `{Types.AreLinks types} :
      Set := {
    from_output : PolymorphicFunction.t;
    from_output_is_method :: IsTraitMethod.C (trait Self) "from_output" from_output;
    run_from_output (output : types.(Types.Output)) :: Run.Trait from_output [] [] [ φ output ] Self;
  }.

  Class Method_branch
      (Self : Set) `{Link Self}
      (types : Types.t) `{Types.AreLinks types} :
      Set := {
    branch : PolymorphicFunction.t;
    branch_is_method :: IsTraitMethod.C (trait Self) "branch" branch;
    run_branch (self : Self) :: Run.Trait branch [] [] [ φ self ] (ControlFlow.t types.(Types.Residual) types.(Types.Output));
  }.

  Class Run (Self : Set) `{Link Self}
      (types : Types.t) `{Types.AreLinks types} :
      Set := {
    run_FromResidual_for_Self :: FromResidual.Run Self types.(Types.Residual);
    method_from_output :: Method_from_output Self types;
    method_branch :: Method_branch Self types;
  }.
End Try.
Export (hints) Try.
