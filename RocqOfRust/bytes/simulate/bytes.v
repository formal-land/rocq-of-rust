Require Import simulate.RocqOfRust.
Require Import bytes.links.bytes.
Require Import core.convert.links.mod.
Require Import core.convert.simulate.mod.
Require Import core.ops.links.deref.
Require Import core.ops.simulate.deref.

Module Impl_Bytes.
  Definition Self : Set :=
    Bytes.t.

  Definition len (self : Self) : usize :=
    {| Integer.value := Z.of_nat (List.length self.(Bytes.value)) |}.

  Lemma len_eq (ref_self : '& Self) (self : Self) (stack : Stack.t) :
      CanRead.t stack self ref_self ->
    {{
      SimulateM.eval_f
        (bytes.Impl_Bytes.run_len ref_self)
        stack 🌲
      (
        Output.Success (len self),
        stack
      )
    }}.
  Proof.
  Admitted.
End Impl_Bytes.
Export (hints) Impl_Bytes.

Module Impl_Deref_for_Bytes.
  Definition Self : Set :=
    Bytes.t.

  Definition deref : RefStub.t Self (list u8) := {|
    RefStub.path := [Pointer.Index.StructRecord "bytes::bytes::Bytes" "ptr"];
    RefStub.projection self := self.(Bytes.value);
    RefStub.injection self value := {| Bytes.value := value |};
  |}.

  Instance I : Deref.C Self (list u8) := {|
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
    Bytes.t.

  Definition as_ref : RefStub.t Self (list u8) :=
    Impl_Deref_for_Bytes.deref.

  Instance I : AsRef.C Self (list u8) := {|
    AsRef.as_ref := as_ref;
  |}.

  Module Eq.
    Instance I : AsRef.Eq.C Impl_AsRef_slice_u8_for_Bytes.I.
    Proof.
      constructor; intros.
      change {{
        SimulateM.eval_f
          (bytes.links.bytes.Impl_AsRef_slice_u8_for_Bytes.run_as_ref ref_self)
          stack 🌲
        (
          Output.Success
            (RefStub.apply ref_self Impl_Deref_for_Bytes.deref),
          stack
        )
      }}.
      with_strategy transparent
        [bytes.links.bytes.Impl_AsRef_slice_u8_for_Bytes.run_as_ref]
        unfold bytes.links.bytes.Impl_AsRef_slice_u8_for_Bytes.run_as_ref.
      exact
        (@Deref.Eq.deref
          Self
          (list u8)
          _
          _
          bytes.links.bytes.Impl_Deref_for_Bytes.run
          Impl_Deref_for_Bytes.I
          Impl_Deref_for_Bytes.Eq.I
          ref_self
          stack).
    Qed.
  End Eq.
  Export (hints) Eq.
End Impl_AsRef_slice_u8_for_Bytes.
Export (hints) Impl_AsRef_slice_u8_for_Bytes.
