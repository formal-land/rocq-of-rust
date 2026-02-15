Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_primitives.links.lib.

(* TODO: check the value *)
Definition KECCAK_EMPTY : aliases.B256.t :=
  alloy_primitives.bits.simulate.fixed.FixedBytes.from_Z
    89477152217924674838424037953991966239322087453347756267410168184682657981552.

Lemma KECCAK_EMPTY_eq (stack : Stack.t) :
  {{
    SimulateM.eval_f run_KECCAK_EMPTY stack 🌲
    (
      Output.Success (Ref.immediate Pointer.Kind.Raw KECCAK_EMPTY),
      stack
    )
  }}.
Admitted.
