Require Import links.RocqOfRust.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.utils.mod.
Require Import core.convert.links.mod.

(* pub fn keccak256<T: AsRef<[u8]>>(bytes: T) -> B256 *)
Instance run_keccak256
  {T : Set} `{Link T}
  {run_AsRef_for_T : AsRef.Run T (list u8)}
  (bytes : T) :
  Run.Trait
    utils.keccak256 [] [ Φ T ] [ φ bytes ]
    aliases.B256.t.
Proof.
  constructor.
  run_symbolic.
Admitted.
Global Opaque run_keccak256.
