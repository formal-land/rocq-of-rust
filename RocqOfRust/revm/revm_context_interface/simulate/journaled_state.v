Require Import simulate.RocqOfRust.
Require Import core.ops.links.deref.
Require Import core.ops.simulate.deref.
Require Import revm.revm_context_interface.links.journaled_state.

Module Impl_Deref_for_StateLoad.
  Definition Self (T : Set) : Set :=
    StateLoad.t T.

  Definition deref {T : Set} `{Link T} : RefStub.t (Self T) T := {|
    RefStub.path := [];
    RefStub.projection x := x.(StateLoad.data);
    RefStub.injection x y := x <| StateLoad.data := y |>;
  |}.

  Lemma deref_eq
      {T : Set} `{Link T}
      (ref_self : '& (Self T))
      (self : Self T)
      (stack : Stack.t) :
    CanRead.t stack self ref_self ->
    {{
      SimulateM.eval_f
        (Deref.run_deref ref_self)
        stack 🌲
      (
        Output.Success (RefStub.apply ref_self deref),
        stack
      )
    }}.
  Admitted.

  Instance I {T : Set} `{Link T} :
      core.ops.simulate.deref.Deref.C (Self T) T := {|
    core.ops.simulate.deref.Deref.deref := deref;
  |}.

  Module Eq.
    Instance I {T : Set} `{Link T} :
      core.ops.simulate.deref.Deref.Eq.t
        (Self := Self T) (Target := T) Impl_Deref_for_StateLoad.I.
    Proof.
    Admitted.
  End Eq.
  Export (hints) Eq.
End Impl_Deref_for_StateLoad.
Export (hints) Impl_Deref_for_StateLoad.

Module Impl_Eip7702CodeLoad.
  Definition Self (T : Set) : Set :=
    Eip7702CodeLoad.t T.

  Definition into_components {T : Set} (self : Self T) : T * Self unit :=
    (
      self.(Eip7702CodeLoad.state_load).(StateLoad.data),
      {|
        Eip7702CodeLoad.state_load := {|
          StateLoad.data := tt;
          StateLoad.is_cold :=
            self.(Eip7702CodeLoad.state_load).(StateLoad.is_cold);
        |};
        Eip7702CodeLoad.is_delegate_account_cold :=
          self.(Eip7702CodeLoad.is_delegate_account_cold);
      |}
    ).

  Lemma into_components_eq
      {T : Set} `{Link T}
      (self : Self T)
      (stack : Stack.t) :
    {{
      SimulateM.eval_f
        (@Impl_Eip7702CodeLoad.run_into_components T _ self)
        stack 🌲
      (
        Output.Success (into_components self),
        stack
      )
    }}.
  Admitted.
End Impl_Eip7702CodeLoad.
Export (hints) Impl_Eip7702CodeLoad.
