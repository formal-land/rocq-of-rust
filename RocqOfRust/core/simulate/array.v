Require Import simulate.RocqOfRust.
Require Import core.links.array.

Definition pointer_coercion_unsize_array_to_slice {A : Set} {N : usize} (array : array.t A N) :
    list A :=
  ArrayPairs.to_list array.(array.value).

Lemma pointer_coercion_unsize_array_to_slice_eq
    {A : Set} `{Link A} {pointer_kind : Pointer.Kind.t} {N : usize}
    (ref_array : Ref.t pointer_kind (array.t A N)) (array : array.t A N)
    (ref_slice : Ref.t pointer_kind (list A))
    (stack : Stack.t) :
  CanRead.t stack array ref_array ->
  CanRead.t stack (pointer_coercion_unsize_array_to_slice array) ref_slice ->
  {{
    SimulateM.eval_f
      (array.run_pointer_coercion_unsize_array_to_slice ref_array)
      stack 🌲
    (
      Output.Success ref_slice,
      stack
    )
  }}.
Proof.
Admitted.

Lemma array_pairs_to_list_injective {A : Set} {n} (xs ys : ArrayPairs.t A n) :
  ArrayPairs.to_list xs = ArrayPairs.to_list ys -> xs = ys.
Proof.
  revert xs ys. induction n as [|n IH].
  - intros [] []; reflexivity.
  - intros [x xs] [y ys] H. cbn in H. injection H as Hxy Htail.
    subst y. f_equal. now apply IH.
Qed.

Lemma array_pairs_to_list_of_list {A : Set} (xs : list A) :
  ArrayPairs.to_list (ArrayPairs.of_list xs) = xs.
Proof. induction xs; cbn; congruence. Qed.
