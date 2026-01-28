Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import RocqOfRust.lib.simulate.lib.
Require Import core.num.links.mod.

Module Impl_u64.
  Definition Self : Set := u64.

  Definition MIN : Self := {| Integer.value := 0 |}.

  Lemma min_eq (stack : Stack.t) :
    {{
      SimulateM.eval_f (Impl_u64.run_min) stack 🌲
      (Output.Success (Ref.immediate Pointer.Kind.Raw MIN), stack)
    }}.
  Proof.
    apply Run.Pure.
  Qed.

  Definition MAX : Self := {| Integer.value := 2 ^ 64 - 1 |}.

  Lemma max_eq (stack : Stack.t) :
    {{
      SimulateM.eval_f (Impl_u64.run_max) stack 🌲
      (Output.Success (Ref.immediate Pointer.Kind.Raw MAX), stack)
    }}.
  Proof.
    repeat (eapply Run.Call || apply Run.Pure).
  Qed.

  Definition overflowing_sub (self other : Self) : Self * bool :=
    let result := BinOp.Wrap.sub self other in
    let overflow :=
      match BinOp.Checked.sub self other with
      | Some result => false
      | None => true
      end in
    (result, overflow).

  Lemma overflowing_sub_eq (self other : Self) (stack : Stack.t) :
    {{
      SimulateM.eval_f (Impl_u64.run_overflowing_sub self other) stack 🌲
      (Output.Success (overflowing_sub self other), stack)
    }}.
  Proof.
  Admitted.
End Impl_u64.
Export (hints) Impl_u64.

Module Impl_usize.
  Definition Self : Set := usize.

  Definition MIN : Self := {| Integer.value := 0 |}.

  Lemma min_eq (stack : Stack.t) :
    {{
      SimulateM.eval_f (Impl_usize.run_min) stack 🌲
      (Output.Success (Ref.immediate Pointer.Kind.Raw MIN), stack)
    }}.
  Proof.
    apply Run.Pure.
  Qed.

  Definition MAX : Self := {| Integer.value := 2 ^ 64 - 1 |}.

  Lemma max_eq (stack : Stack.t) :
    {{
      SimulateM.eval_f (Impl_usize.run_max) stack 🌲
      (Output.Success (Ref.immediate Pointer.Kind.Raw MAX), stack)
    }}.
  Proof.
    repeat (eapply Run.Call || apply Run.Pure).
  Qed.
End Impl_usize.
Export (hints) Impl_usize.
