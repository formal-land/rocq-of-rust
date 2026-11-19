Require Import RocqOfRust.simulate.RocqOfRust RocqOfRust.alloc.vec.simulate.mod.
Require Import RocqOfRust.alloc.vec.links.mod RocqOfRust.alloc.links.raw_vec.
Import Vec.
Example zst_bound : max_slice_len 0 = 18446744073709551615.
Proof. reflexivity. Qed.
Example two_byte_bound : max_slice_len 2 = 4611686018427387903.
Proof. reflexivity. Qed.
Section Observations.
  Context {T A : Set} `{Link T} `{Link A} (storage : RawVec.t T A).
  Definition with_length (n : Z) : Vec.t T A := {| Vec.buf := storage; Vec.len := n |}.
  Example empty_vector (size : size_of (Φ T) = 2) :
    {{ SimulateM.eval_f (Impl_Vec_T_A.run_is_empty (Ref.immediate Pointer.Kind.Ref (with_length 0)))
       []%stack 🌲 (Output.Success true, []%stack) }}.
  Proof.
    apply (Impl_Vec_T_A.is_empty_eq []%stack _ (with_length 0)); [constructor |].
    unfold valid_length. rewrite size. split; discriminate || reflexivity.
  Qed.
  Example max_length_zst (size : size_of (Φ T) = 0) :
    let n := Integer.max IntegerKind.Usize in
    {{ SimulateM.eval_f (Impl_Vec_T_A.run_len (Ref.immediate Pointer.Kind.Ref (with_length n)))
       []%stack 🌲 (Output.Success (n : usize), []%stack) }}.
  Proof.
    intro n. apply (Impl_Vec_T_A.len_eq []%stack _ (with_length n)); [constructor |].
    unfold valid_length. rewrite size. split; discriminate || reflexivity.
  Qed.
End Observations.
