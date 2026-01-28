Require Import links.RocqOfRust.

(* pub struct Request<'a>(Tagged<dyn Erased<'a> + 'a>); *)
Module Request.
  Parameter t : Set.

  Parameter to_value : t -> Value.t.

  Instance IsLink : Link t := {
    Φ := Ty.path "core::error::Request";
    φ := to_value;
  }.

  Definition of_ty : OfTy.t (Ty.path "core::error::Request").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End Request.
Export (hints) Request.

(*
pub trait Error: Debug + Display {
    // Provided methods
    fn source(&self) -> Option<&(dyn Error + 'static)> { ... }
    fn description(&self) -> &str { ... }
    fn cause(&self) -> Option<&dyn Error> { ... }
    fn provide<'a>(&'a self, request: &mut Request<'a>) { ... }
}
*)
Module Error.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::error::Error";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_description (Self : Set) `{Link Self} : Set := {
    description : PolymorphicFunction.t;
    description_is_method :: IsTraitMethod.C (trait Self) "description" description;
    run_description (self : '& Self) :: Run.Trait description [] [] [ φ self ] ('& string);
  }.

  Class Method_provide (Self : Set) `{Link Self} : Set := {
    provide : PolymorphicFunction.t;
    provide_is_method :: IsTraitMethod.C (trait Self) "provide" provide;
    run_provide (self : '& Self) (request : '&mut Request.t) ::
      Run.Trait provide [] [] [ φ self; φ request ] unit;
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    (* TODO: Add source *)
    method_description :: Method_description Self;
    (* TODO: Add cause *)
    method_provide :: Method_provide Self;
  }.
End Error.
Export (hints) Error.
