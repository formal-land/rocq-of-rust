Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.links.mod.

Module Impl_Bytes.
  Definition Self : Set :=
    Bytes.t.

  Definition new : Self :=
    {| Bytes.value := [] |}.

  Lemma new_eq (stack : Stack.t) :
    {{
      SimulateM.eval_f
        links.mod.Impl_Bytes.run_new
        stack 🌲
      (
        Output.Success new,
        stack
      )
    }}.
  Admitted.

  Definition copy_from_slice (data : list u8) : Self :=
    {| Bytes.value := data |}.

  Lemma copy_from_slice_eq (ref_data : '& (list u8)) (stack : Stack.t) (data : list u8) :
      CanRead.t stack data ref_data ->
    {{
      SimulateM.eval_f
        (links.mod.Impl_Bytes.run_copy_from_slice ref_data)
        stack 🌲
      (
        Output.Success (copy_from_slice data),
        stack
      )
    }}.
  Admitted.
End Impl_Bytes.
