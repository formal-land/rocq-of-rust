Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bytes.links.mod.
Require Import bytes.links.bytes.
Require Import core.ops.links.range.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.

Module CallInput.
  Definition range_len (range : Range.t usize) : usize :=
    range.(Range.end_) -i range.(Range.start).

  Definition bytes_len (input_bytes : alloy_primitives.bytes.links.mod.Bytes.t) : usize :=
    {| Integer.value :=
      Z.of_nat
        (List.length
          input_bytes.(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value))
    |}.

  Definition bytes_as_ref (input_bytes : alloy_primitives.bytes.links.mod.Bytes.t) : list u8 :=
    input_bytes.(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value).

  Definition len (self : call_inputs.CallInput.t) : usize :=
    match self with
    | call_inputs.CallInput.SharedBuffer range => range_len range
    | call_inputs.CallInput.Bytes bytes => bytes_len bytes
    end.

  Lemma len_eq
      (ref_self : '& call_inputs.CallInput.t)
      (self : call_inputs.CallInput.t)
      (stack : Stack.t) :
    CanRead.t stack self ref_self ->
    {{
      SimulateM.eval_f
        (call_inputs.Impl_CallInput.run_len ref_self)
        stack 🌲
      (
        Output.Success (len self),
        stack
      )
    }}.
  Admitted.
End CallInput.
