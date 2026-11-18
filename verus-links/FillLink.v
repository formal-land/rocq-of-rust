Require Import RocqOfRust.simulate.RocqOfRust.
Require Import Assertion fill SliceIndex.
Open Scope string_scope.

Definition linked_function : String.string := "fill::fill_prefix".
Definition linked_site : String.string := "contract".
Definition observed_paths :=
  [SlicePath Entry ["xs"]; SlicePath Current ["xs"]; SlicePath Expiry ["xs"];
   WordPath Current ["n"]; WordPath Current ["value"]; WordPath Current ["i"]].

Definition fill_run (xs : '&mut (list u32)) (n : usize) (v : u32) :
  Run.Trait fill_prefix [] [] [φ xs; φ n; φ v] unit.
Proof. constructor. run_symbolic. Defined.

Definition fill_observations (initial current final : list u32)
    (n : usize) (v : u32) (i : Z) : observations :=
  {| word_at _ path :=
       match path with
       | ["n"] => n.(Integer.value)
       | ["value"] => v.(Integer.value)
       | ["i"] => i
       | _ => 0
       end;
     slice_at phase path :=
       match path with
       | ["xs"] => List.map (@Integer.value IntegerKind.U32)
           (match phase with Entry => initial | Current => current | Expiry => final end)
       | _ => []
       end |}.

(** The slice occupies slot zero. A successful run restores the complete caller
    frame after dropping its local counter. The model stores a usize in Z, so
    quantify over its Rust range on the 64-bit target. *)
Definition execution_claim (requires ensures : observations -> Prop) : Prop :=
  forall (initial : list u32) (n : usize) (v : u32) (frame : Stack.t),
    0 <= n.(Integer.value) < 2^64 ->
    requires (fill_observations initial initial initial n v 0) ->
    exists final : list u32,
      {{ SimulateM.eval_f (fill_run (make_ref 0) n v) (initial :: frame)%stack 🌲
         (Output.Success tt, (final :: frame)%stack) }} /\
      ensures (fill_observations initial final final n v n.(Integer.value)).
