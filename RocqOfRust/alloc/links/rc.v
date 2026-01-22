Require Import RocqOfRust.RocqOfRust.
Require Import links.M.
Require Import alloc.rc.
Require Import alloc.links.alloc.
Require Import core.ops.links.deref.

Module Rc.
  Record t {T A : Set} : Set := {
    value : T;
  }.
  Arguments t : clear implicits.

  Parameter to_value : forall {T A : Set}, t T A -> Value.t.

  Global Instance IsLink (T A : Set) `{Link T} `{Link A} : Link (t T A) := {
    Φ := Ty.apply (Ty.path "alloc::rc::Rc") [] [ Φ T; Φ A ];
    φ := to_value;
  }.

  Definition of_ty (T_ty A_ty : Ty.t) :
    OfTy.t T_ty ->
    OfTy.t A_ty ->
    OfTy.t (Ty.apply (Ty.path "alloc::rc::Rc") [] [ T_ty; A_ty ]).
  Proof.
    intros [T] [A].
    eapply OfTy.Make with (A := t T A).
    now subst.
  Defined.
  Smpl Add eapply of_ty : of_ty.
End Rc.
Export (hints) Rc.

Module Impl_Rc.
  Definition Self (T : Set) : Set :=
    Rc.t T Global.t.

  Instance run_new {T : Set} `{Link T} (x : T) :
    Run.Trait
      (rc.Impl_alloc_rc_Rc_T_alloc_alloc_Global.new (Φ T)) [] [] [ φ x ]
      (Self T).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
  Global Opaque run_new.
End Impl_Rc.
Export (hints) Impl_Rc.

(*
  impl<T: ?Sized, A: Allocator> Deref for Rc<T, A> {
      type Target = T;
*)
Module Impl_Deref_for_Rc.
  Instance run_deref {T A : Set} `{Link T} `{Link A} (self : '& (Rc.t T A)) :
    Run.Trait
      (rc.Impl_core_ops_deref_Deref_where_core_marker_Sized_T_where_core_alloc_Allocator_A_for_alloc_rc_Rc_T_A.deref (Φ T) (Φ A))
      [] [] [φ self] ('& T).
  Admitted.
  Global Opaque run_deref.

  Instance method_deref (T A : Set) `{Link T} `{Link A} : Deref.Method_deref (Rc.t T A) T.
  Proof.
    eexists.
    { constructor.
      eapply IsTraitMethod.Defined.
      { apply rc.Impl_core_ops_deref_Deref_where_core_marker_Sized_T_where_core_alloc_Allocator_A_for_alloc_rc_Rc_T_A.Implements. }
      { reflexivity. }
    }
    { typeclasses eauto. }
  Defined.

  Instance run (T A : Set) `{Link T} `{Link A} : Deref.Run (Rc.t T A) T := {}.
End Impl_Deref_for_Rc.
Export (hints) Impl_Deref_for_Rc.

