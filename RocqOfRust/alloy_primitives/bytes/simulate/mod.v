Require Import simulate.RocqOfRust.
Require Import alloc.links.alloc.
Require Import alloc.links.raw_vec.
Require Import alloc.vec.links.mod.
Require Import alloy_primitives.bytes.links.mod.
Require Import bytes.links.bytes.
Require Import bytes.simulate.bytes.
Require Import core.convert.links.mod.
Require Import core.convert.simulate.mod.
Require Import core.links.clone.
Require Import core.ops.links.deref.
Require Import core.ops.simulate.deref.

Module Impl_Bytes.
  Definition Self : Set :=
    bytes.links.mod.Bytes.t.

  Definition new : Self :=
    {| bytes.links.mod.Bytes.value := {| bytes.Bytes.value := [] |} |}.

  Lemma new_eq (stack : Stack.t) :
    {{
      SimulateM.eval_f
        links.mod.Impl_Bytes.run_new
        stack 🌲
      (
        Output.Success new,
        stack
      )
    }}.
  Proof.
  Admitted.

  Definition copy_from_slice (data : list u8) : Self :=
    {| bytes.links.mod.Bytes.value := {| bytes.Bytes.value := data |} |}.

  Lemma copy_from_slice_eq (ref_data : '& (list u8)) (stack : Stack.t) (data : list u8) :
      CanRead.t stack data ref_data ->
    {{
      SimulateM.eval_f
        (links.mod.Impl_Bytes.run_copy_from_slice ref_data)
        stack 🌲
      (
        Output.Success (copy_from_slice data),
        stack
      )
    }}.
  Proof.
  Admitted.
End Impl_Bytes.

Module Impl_Clone_for_Bytes.
  Definition Self : Set :=
    bytes.links.mod.Bytes.t.

  Definition clone (self : Self) : Self := {|
    bytes.links.mod.Bytes.value := self.(bytes.links.mod.Bytes.value);
  |}.

  Lemma clone_eq
      (ref_self : '& Self)
      (self : Self)
      (stack : Stack.t) :
    CanRead.t stack self ref_self ->
    {{
      SimulateM.eval_f
        (Clone.run_clone (Self := Self) ref_self)
        stack 🌲
      (
        Output.Success (clone self),
        stack
      )
    }}.
  Proof.
  Admitted.
End Impl_Clone_for_Bytes.
Export (hints) Impl_Clone_for_Bytes.

Module Impl_Default_for_Bytes.
  Definition Self : Set :=
    bytes.links.mod.Bytes.t.

  Definition default : Self :=
    Impl_Bytes.new.

  Lemma default_eq (stack : Stack.t) :
    {{
      SimulateM.eval_f
        links.mod.Impl_Default_for_Bytes.run_default
        stack 🌲
      (
        Output.Success default,
        stack
      )
    }}.
  Proof.
  Admitted.
End Impl_Default_for_Bytes.
Export (hints) Impl_Default_for_Bytes.

Module Impl_Deref_for_Bytes.
  Definition Self : Set :=
    bytes.links.mod.Bytes.t.

  Definition deref : RefStub.t Self bytes.Bytes.t := {|
    RefStub.path := [
      Pointer.Index.Array 0
    ];
    RefStub.projection self := self.(bytes.links.mod.Bytes.value);
    RefStub.injection self value := {| bytes.links.mod.Bytes.value := value |};
  |}.

  Instance I : Deref.C Self bytes.Bytes.t := {|
    Deref.deref := deref;
  |}.

  Module Eq.
    Instance I : Deref.Eq.t I.
    Proof.
    Admitted.
  End Eq.
  Export (hints) Eq.
End Impl_Deref_for_Bytes.
Export (hints) Impl_Deref_for_Bytes.

Module Impl_AsRef_slice_u8_for_Bytes.
  Definition Self : Set :=
    bytes.links.mod.Bytes.t.

  Definition as_ref (ref_self : '& Self) : '& (list u8) :=
    let ref_bytes_raw : '* bytes.Bytes.t := {|
      Ref.core :=
        SubPointer.Runner.apply
          ref_self.(Ref.core)
          links.mod.Bytes.SubPointer.get_0;
    |} in
    let ref_bytes : '& bytes.Bytes.t :=
      Ref.cast_to Pointer.Kind.Ref ref_bytes_raw in
    Ref.cast_to Pointer.Kind.Ref
      (RefStub.apply
        (kind_target := Pointer.Kind.Raw)
        ref_bytes
        bytes.simulate.bytes.Impl_AsRef_slice_u8_for_Bytes.as_ref).

  Lemma as_ref_eq
      (ref_self : '& Self)
      (stack : Stack.t)
      (self : Self) :
    CanRead.t stack self ref_self ->
    {{
      SimulateM.eval_f
        (links.mod.Impl_AsRef_slice_u8_for_Bytes.run_as_ref ref_self)
        stack 🌲
      (
        Output.Success (as_ref ref_self),
        stack
      )
    }}.
  Proof.
    intros H_can_read.
    unfold as_ref.
    with_strategy transparent
      [links.mod.Impl_AsRef_slice_u8_for_Bytes.run_as_ref] cbn.
    s. {
      apply bytes.simulate.bytes.Impl_AsRef_slice_u8_for_Bytes.Eq.I.
    }
    s.
  Qed.

  Lemma can_read_as_ref
      (ref_self : '& Self)
      (stack : Stack.t)
      (self : Self) :
    CanRead.t stack self ref_self ->
    CanRead.t
      stack
      self.(bytes.links.mod.Bytes.value).(bytes.Bytes.value)
      (as_ref ref_self).
  Proof.
    intros H_read.
    destruct H_read.
    - unfold as_ref; cbn.
      constructor.
    - destruct run.
      unfold as_ref; cbn.
      unshelve eapply CanRead.Mutable.
      + constructor.
        exact nth.
      + cbn.
        cbn in H.
        now rewrite H.
  Qed.
End Impl_AsRef_slice_u8_for_Bytes.
Export (hints) Impl_AsRef_slice_u8_for_Bytes.

Module Impl_DerefMut_for_Bytes.
  Definition Self : Set :=
    bytes.links.mod.Bytes.t.

  Definition deref_mut : RefStub.t Self bytes.Bytes.t := {|
    RefStub.path := [
      Pointer.Index.Array 0
    ];
    RefStub.projection self := self.(bytes.links.mod.Bytes.value);
    RefStub.injection self value := {| bytes.links.mod.Bytes.value := value |};
  |}.

  Instance I : DerefMut.C Self bytes.Bytes.t := {|
    DerefMut.deref_mut := deref_mut;
  |}.

  Module Eq.
    Instance I : DerefMut.Eq.t I.
    Proof.
    Admitted.
  End Eq.
  Export (hints) Eq.
End Impl_DerefMut_for_Bytes.
Export (hints) Impl_DerefMut_for_Bytes.

Module Impl_From_Vec_u8_for_Bytes.
  Definition Self : Set :=
    bytes.links.mod.Bytes.t.

  Definition from (value : Vec.t u8 Global.t) : Self :=
    {| bytes.links.mod.Bytes.value := {| bytes.Bytes.value := value.(Vec.buf).(RawVec.value) |} |}.

  Lemma from_eq (value : Vec.t u8 Global.t) (stack : Stack.t) :
    {{
      SimulateM.eval_f
        (From.run_from value)
        stack 🌲
      (
        Output.Success (from value),
        stack
      )
    }}.
  Proof.
  Admitted.

  Instance I : From.C Self (Vec.t u8 Global.t) := {|
    From.from := from;
  |}.

  Module Eq.
    Instance I : From.Eq.C (Self := Self) (T := Vec.t u8 Global.t) I.
    Proof.
      constructor; intros.
      (* from *)
      { apply from_eq. }
    Qed.
  End Eq.
  Export (hints) Eq.
End Impl_From_Vec_u8_for_Bytes.
Export (hints) Impl_From_Vec_u8_for_Bytes.
