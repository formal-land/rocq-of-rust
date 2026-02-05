Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.simulate.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_interpreter.instructions.links.utility.
Require Import ruint.links.lib.

Definition cast_slice_to_u256 (slice : list u8) : aliases.U256.t :=
  {|
    Uint.value := List.fold_left (fun acc byte => (acc * 256) + i[byte])%Z slice 0;
  |}.

Lemma cast_slice_to_address_like
    (stack : Stack.t)
    (slice : '& (list u8))
    (dest : '&mut aliases.U256.t) :
  SimulateM.eval_f
    (run_cast_slice_to_u256 slice dest)
    stack =
  let*s slice := SimulateM.read stack slice.(Ref.core) in
  match slice with
  | Output.Success slice =>
    let*s stack' := SimulateM.write stack dest.(Ref.core) (cast_slice_to_u256 slice) in
    match stack' with
    | Output.Success stack' =>
      SimulateM.Pure (Output.Success tt, stack')
    | Output.Exception exception =>
      SimulateM.Pure (Output.Exception exception, stack)
    end
  | Output.Exception exception =>
    SimulateM.Pure (Output.Exception exception, stack)
  end.
Admitted.

Module Impl_IntoAddress_for_U256.
  Definition into_address (self : aliases.U256.t) : Address.t :=
    Impl_Address.from_word (Impl_From_U256_for_FixedBytes_32.from self).

  Lemma into_address_eq (self : aliases.U256.t) (stack : Stack.t) :
    {{
      SimulateM.eval_f
        (Impl_IntoAddress_for_U256.run_into_address self)
        stack 🌲
      (Output.Success (into_address self), stack)
    }}.
  Proof.
  Admitted.
End Impl_IntoAddress_for_U256.
