Require Import RocqOfRust.simulate.RocqOfRust.
Require Import nested Assertion.
Import ListNotations.
Open Scope pstring_scope.

Module Pair.
  RocqOfRustLinkRecord "nested::Pair" := { left : u32; right : u32 }.
End Pair.
Import (hints) Pair.
Module Outer.
  RocqOfRustLinkRecord "nested::Outer" := { pair : Pair.t; sentinel : u32 }.
End Outer.
Import (hints) Outer.

Definition root : '&mut Outer.t := make_ref 0.
Definition inner_ref : '&mut Pair.t :=
  {| Ref.core := SubPointer.Runner.apply root.(Ref.core) Outer.SubPointer.get_pair |}.
Definition left_ref : '&mut u32 :=
  {| Ref.core := SubPointer.Runner.apply inner_ref.(Ref.core) Pair.SubPointer.get_left |}.

#[export] Instance run_swap (p : '&mut Outer.t) : Run.Trait swap [] [] [φ p] unit.
Proof. constructor; run_symbolic. Defined.
#[export] Instance run_left (p : '&mut Outer.t) : Run.Trait left_mut [] [] [φ p] ('&mut u32).
Proof. constructor; run_symbolic. Defined.
#[export] Instance run_twice (p : '&mut Outer.t) (a b : u32) :
  Run.Trait write_twice [] [] [φ p; φ a; φ b] unit.
Proof. constructor; run_symbolic. Defined.

Open Scope string_scope.
Definition snapshot (o : Outer.t) (fields : list String.string) : Z :=
  match fields with
  | ["pair"; "left"] => Integer.value (Pair.left (Outer.pair o))
  | ["pair"; "right"] => Integer.value (Pair.right (Outer.pair o))
  | ["sentinel"] => Integer.value (Outer.sentinel o)
  | _ => 0%Z
  end.

Definition memory_view (initial final : Outer.t)
    (other : phase -> list String.string -> Z) : observations :=
  {| word_at := fun p path => match path with
     | "p" :: fields => snapshot (match p with Expiry => final | _ => initial end) fields
     | _ => other p path
     end;
     slice_at := fun _ _ => [] |}.

Definition record_paths (p : phase) : list access :=
  [WordPath p ["p"; "pair"; "left"]; WordPath p ["p"; "pair"; "right"];
   WordPath p ["p"; "sentinel"]].
Definition nested_paths := (record_paths Entry ++ record_paths Expiry)%list.
Ltac execute := repeat (cbn || get_can_access || eapply Run.Call || apply Run.LetUnfold || apply Run.Pure).
