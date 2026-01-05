Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.links.array.

(* pub struct FixedBytes<const N: usize>(pub [u8; N]); *)
Module FixedBytes.
  Record t {N : usize} : Set := {
    value : array.t u8 N;
  }.
  Arguments t : clear implicits.

  Global Instance IsLink (N : usize) : Link (t N) := {
    Φ := Ty.apply (Ty.path "alloy_primitives::bits::fixed::FixedBytes") [ φ N ] [];
    φ x := Value.StructTuple "alloy_primitives::bits::fixed::FixedBytes" [φ N] [] [φ x.(value)];
  }.

  Definition of_ty (N' : Value.t) (N : usize) :
    N' = φ N ->
    OfTy.t (Ty.apply (Ty.path "alloy_primitives::bits::fixed::FixedBytes") [ N' ] []).
  Proof.
    intros.
    eapply OfTy.Make with (A := t N).
    now subst.
  Defined.
  Smpl Add unshelve eapply of_ty : of_ty.

  Lemma of_value_with (N' : Value.t) (N : usize) (value : array.t u8 N) (value' : Value.t) :
    N' = φ N ->
    value' = φ value ->
    Value.StructTuple "alloy_primitives::bits::fixed::FixedBytes" [N'] [] [value'] =
    φ (Build_t N value).
  Proof.
    now intros; subst.
  Qed.
  Smpl Add unshelve eapply of_value_with : of_value.

  Definition of_value (N' : Value.t) (N : usize) (value' : Value.t) (value : array.t u8 N) :
    N' = φ N ->
    value' = φ value ->
    OfValue.t (Value.StructTuple "alloy_primitives::bits::fixed::FixedBytes" [N'] [] [value']).
  Proof.
    intros.
    eapply OfValue.Make with (A := t N) (value := Build_t N value).
    now subst.
  Defined.
  Smpl Add unshelve eapply of_value : of_value.

  Module SubPointer.
    Definition get_0 (N : usize) : SubPointer.Runner.t (t N)
      (Pointer.Index.StructTuple "alloy_primitives::bits::fixed::FixedBytes" 0) :=
    {|
      SubPointer.Runner.projection x := Some x.(value);
      SubPointer.Runner.injection x y := Some (x <| value := y |>);
    |}.

    Lemma get_0_is_valid {N : usize} :
      SubPointer.Runner.Valid.t (get_0 N).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_0_is_valid : run_sub_pointer.
  End SubPointer.
End FixedBytes.
