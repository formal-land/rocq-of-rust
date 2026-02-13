Require Import simulate.RocqOfRust.
Require Import bytes.links.bytes.
Require Import core.ops.links.deref.
Require Import core.ops.simulate.deref.

Class Execute {A : Set} (e : SimulateM.t A) (value : A) : Prop := {
  foo : {{
    e 🌲
    value
  }}
}.

Class Foo (P : Prop) : Prop := {
  Provided : Prop;
  provided : Provided;
}.

Class FooFlat (P : Prop) (Provided : Prop -> Prop) : Prop := {
  provided : Provided P;
}.

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
  Admitted.

  Class Gre (P : Prop) : Prop := {
    gre : True;
  }.

  Instance len_Execute (ref_self : '& Bytes.t) (self : Bytes.t) (stack : Stack.t)
  (* CanRead.t stack self ref_self -> *)
  `{Gre (CanRead.t stack self ref_self)} :
    Execute
      (* (SimulateM.eval (evaluate (bytes.Impl_Bytes.run_len ref_self).(Run.run_f)) stack) *)
      (SimulateM.eval_f
      (bytes.Impl_Bytes.run_len ref_self)
      stack)
      (
        Output.Success (len self),
        stack
      ).
  Admitted.

  Instance len_Foo (ref_self : '& Self) (self : Self) (stack : Stack.t) :
      Foo
    {{
      SimulateM.eval_f
        (bytes.Impl_Bytes.run_len ref_self)
        stack 🌲
      (
        Output.Success (len self),
        stack
      )
    }} :=
  {
    provided := len_eq ref_self self stack
  }.

  (* Instance len_FooFlat (ref_self : '& Self) (self : Self) (stack : Stack.t) :
    FooFlat
    {{
      SimulateM.eval_f
        (bytes.Impl_Bytes.run_len ref_self)
        stack 🌲
      (
        Output.Success (len self),
        stack
      )
    }}
    _ :=
  {
    provided
      () := len_eq ref_self self stack
  }. *)

  Instance len_FooFlat (ref_self : '& Self) (self : Self) (stack : Stack.t) :
    FooFlat
      {{
        SimulateM.eval_f
          (bytes.Impl_Bytes.run_len ref_self)
          stack 🌲
        (
          Output.Success (len self),
          stack
        )
      }}
      (fun P => CanRead.t stack self ref_self -> P).
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
    Instance t : Deref.Eq.t I.
    Admitted.
  End Eq.
  Export (hints) Eq.
End Impl_Deref_for_Bytes.
Export (hints) Impl_Deref_for_Bytes.
