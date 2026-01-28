Require Import links.RocqOfRust.
Require Import core.ops.function.

(*
    pub trait FnOnce<Args: Tuple> {
        type Output;

        // Required method
        extern "rust-call" fn call_once(self, args: Args) -> Self::Output;
    }
*)
Module FnOnce.
  Definition trait (Self Args : Set) `{Link Self} `{Link Args} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::ops::function::FnOnce";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [Φ Args];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_call_once (Self Args Output : Set)
      `{Link Self} `{Link Args} `{Link Output} : Set := {
    call_once : PolymorphicFunction.t;
    call_once_is_method :: IsTraitMethod.C (trait Self Args) "call_once" call_once;
    run_call_once (self : Self) (args : Args) ::
      Run.Trait call_once [] [] [ φ self; φ args ] Output;
  }.

  Class Run (Self Args Output : Set)
      `{Link Self} `{Link Args} `{Link Output} : Set := {
    method_call_once :: Method_call_once Self Args Output;
  }.
End FnOnce.
Export (hints) FnOnce.

Module Impl_FnOnce_for_Function2.
  Instance method_call_once (A1 A2 Output: Set) `{Link A1} `{Link A2} `{Link Output} :
    FnOnce.Method_call_once (Function2.t A1 A2 Output) (A1 * A2) Output.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply FunctionTraitAutomaticImpl.FunctionImplementsFnOnce. }
      { reflexivity. }
    }
    { constructor.
      destruct args as [a1 a2].
      with_strategy transparent [φ] cbn.
      run_symbolic_closure_auto.
      run_symbolic.
    }
  Defined.

  Instance run (A1 A2 Output: Set) `{Link A1} `{Link A2} `{Link Output} :
    FnOnce.Run (Function2.t A1 A2 Output) (A1 * A2) Output :=
  {}.
End Impl_FnOnce_for_Function2.
Export (hints) Impl_FnOnce_for_Function2.

(*
pub trait FnMut<Args: Tuple>: FnOnce<Args> {
    extern "rust-call" fn call_mut(&mut self, args: Args) -> Self::Output;
}
*)
Module FnMut.
  Definition trait (Self Args : Set) `{Link Self} `{Link Args} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "core::ops::function::FnMut";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [Φ Args];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_call_mut (Self Args Output : Set)
      `{Link Self} `{Link Args} `{Link Output} : Set := {
    call_mut : PolymorphicFunction.t;
    call_mut_is_method :: IsTraitMethod.C (trait Self Args) "call_mut" call_mut;
    run_call_mut (self : '&mut Self) (args : Args) ::
      Run.Trait call_mut [] [] [ φ self; φ args ] Output;
  }.

  Class Run (Self Args Output : Set)
      `{Link Self} `{Link Args} `{Link Output} : Set := {
    run_FnOnce_for_Self :: FnOnce.Run Self Args Output;
    method_call_mut :: Method_call_mut Self Args Output;
  }.
End FnMut.
Export (hints) FnMut.

Module Impl_FnMut_for_Function1.
  Instance run (A Output : Set) `{Link A} `{Link Output} :
      FnMut.Run (Function1.t A Output) A Output.
  Admitted.
End Impl_FnMut_for_Function1.
Export (hints) Impl_FnMut_for_Function1.
