Require Import RocqOfRust.simulate.RocqOfRust RocqOfRust.core.slice.simulate.mod.
Require Import RocqOfRust.core.slice.links.mod.
Example empty_bytes :
  {{ SimulateM.eval_f (Impl_Slice.run_is_empty (Ref.immediate Pointer.Kind.Ref ([] : list u8)))
     []%stack 🌲 (Output.Success true, []%stack) }}.
Proof. eapply Impl_Slice.is_empty_eq. constructor. Qed.
Example two_bytes :
  {{ SimulateM.eval_f (Impl_Slice.run_len (Ref.immediate Pointer.Kind.Ref ([3;4] : list u8)))
     []%stack 🌲 (Output.Success (2 : usize), []%stack) }}.
Proof. eapply Impl_Slice.len_eq. constructor. Qed.
Example zero_sized_elements :
  {{ SimulateM.eval_f (Impl_Slice.run_len (Ref.immediate Pointer.Kind.Ref [tt;tt;tt]))
     []%stack 🌲 (Output.Success (3 : usize), []%stack) }}.
Proof. eapply Impl_Slice.len_eq. constructor. Qed.
