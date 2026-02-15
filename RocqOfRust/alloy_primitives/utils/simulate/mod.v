Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.utils.links.mod.
Require Import core.convert.links.mod.
Require Import core.convert.simulate.mod.

Parameter keccak256_primitive : list u8 -> aliases.B256.t.

Definition keccak256
    {T : Set} `{Link T}
    `{AsRef_for_T : !AsRef.C T (list u8)}
    (bytes : T) :
    aliases.B256.t :=
  let bytes := AsRef.as_ref.(RefStub.projection) bytes in
  keccak256_primitive bytes.

Lemma keccak256_eq
    {T : Set} `{Link T}
    `{!AsRef.Run T (list u8)}
    `{AsRef_for_T : !AsRef.C T (list u8)}
    `{!AsRef.Eq.C AsRef_for_T}
    (bytes : T)
    (stack : Stack.t) :
  {{
    SimulateM.eval_f
      (links.mod.run_keccak256 bytes)
      stack 🌲
    (
      Output.Success (keccak256 bytes),
      stack
    )
  }}.
Admitted.
