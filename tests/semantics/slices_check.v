Require Import RocqOfRust.simulate.RocqOfRust RocqOfRust.core.slice.simulate.mod.
Require Import RocqOfRust.core.slice.links.mod.
Example empty_bytes :
  {{ SimulateM.eval_f (Impl_Slice.run_is_empty (Ref.immediate Pointer.Kind.Ref ([] : list u8)))
     []%stack 🌲 (Output.Success true, []%stack) }}.
Proof. apply (Impl_Slice.is_empty_eq []%stack _ ([] : list u8)). constructor. Qed.
Example two_bytes :
  {{ SimulateM.eval_f (Impl_Slice.run_len (Ref.immediate Pointer.Kind.Ref [(3 : u8); (4 : u8)]))
     []%stack 🌲 (Output.Success (2 : usize), []%stack) }}.
Proof. apply (Impl_Slice.len_eq []%stack _ [(3 : u8); (4 : u8)]). constructor. Qed.
Example zero_sized_elements :
  {{ SimulateM.eval_f (Impl_Slice.run_len (Ref.immediate Pointer.Kind.Ref [tt;tt;tt]))
     []%stack 🌲 (Output.Success (3 : usize), []%stack) }}.
Proof. apply (Impl_Slice.len_eq []%stack _ [tt;tt;tt]). constructor. Qed.
