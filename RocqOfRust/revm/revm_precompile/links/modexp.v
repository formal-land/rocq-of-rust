Require Import links.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.cmp.
Require Import core.num.links.mod.
Require Import revm.revm_precompile.modexp.
Require Import ruint.links.lib.
Require Import ruint.links.cmp.
Require Import ruint.links.bits.

(* pub fn calculate_iteration_count<const MULTIPLIER: u64>(
     exp_length: u64,
     exp_highp: &U256
   ) -> u64 *)

Instance run_calculate_iteration_count
    (MULTIPLIER : u64)
    (exp_length : u64)
    (exp_highp : '& aliases.U256.t) :
  Run.Trait
    modexp.calculate_iteration_count
    [ φ MULTIPLIER ]
    []
    [ φ exp_length; φ exp_highp ]
    u64.
Proof.
  constructor.
  run_symbolic.
Defined.

Global Opaque run_calculate_iteration_count.