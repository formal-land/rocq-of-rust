Require Import links.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.cmp.
Require Import core.num.links.mod.
Require Import core.ops.links.function.
Require Import revm.revm_precompile.modexp.
Require Import ruint.links.lib.
Require Import ruint.links.cmp.
Require Import ruint.links.bits.
Require Import ruint.links.from.
Require Import ruint.links.macros.

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

(* pub fn gas_calc<const MIN_PRICE: u64, const MULTIPLIER: u64,
     const GAS_DIVISOR: u64, F>(...) -> u64 *)

Instance run_gas_calc
    (MIN_PRICE MULTIPLIER GAS_DIVISOR : u64)
    (F : Set)
    `{Link F}
    (Run_Fn_for_F : function.Fn.Run F (OneElementTuple.t u64) aliases.U256.t)
    (base_len exp_len mod_len : u64)
    (exp_highp : '& aliases.U256.t)
    (calculate_multiplication_complexity : F) :
  Run.Trait
    modexp.gas_calc
    [ φ MIN_PRICE; φ MULTIPLIER; φ GAS_DIVISOR ]
    [ Φ F ]
    [
      φ base_len;
      φ exp_len;
      φ mod_len;
      φ exp_highp;
      φ calculate_multiplication_complexity
    ]
    u64.
Proof.
  constructor.
  destruct (Impl_Div_for_Uint_Uint.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  destruct (Impl_Mul_for_Uint_Uint.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  run_symbolic.
  1: eapply Run.CallPrimitiveGetTraitMethod.
  1: exact Run_Fn_for_F.(function.Fn.method_call).(function.Fn.call_is_method).(IsTraitMethod.Make).
  1: run_symbolic.
Defined.

Global Opaque run_gas_calc.

(* pub fn berlin_gas_calc(base_len: u64, exp_len: u64, mod_len: u64, exp_highp: &U256) -> u64 *)
Instance run_berlin_gas_calc
    (base_len exp_len mod_len : u64)
    (exp_highp : '& aliases.U256.t) :
  Run.Trait
    modexp.berlin_gas_calc
    [] []
    [ φ base_len; φ exp_len; φ mod_len; φ exp_highp ]
    u64.
Proof.
  constructor.
  run_symbolic.
  match goal with
  | |- context [Value.Closure (existS (_, _) ?body)] =>
    unshelve epose proof (run_gas_calc
      {| Integer.value := 200 |} {| Integer.value := 8 |} {| Integer.value := 3 |}
      (Function1.t u64 aliases.U256.t)
      (function.Impl_Fn_for_Function1.run u64 aliases.U256.t)
      value value0 value1 (Ref.cast_to Pointer.Kind.Ref value2)
      {| Function1.f := body; Function1.run := _ |}) as H_gas_calc
  end.
  2: exact H_gas_calc.
  intros a.
  cbn beta iota.
  destruct (Impl_Mul_for_Uint_Uint.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  run_symbolic.
Defined.

Global Opaque run_berlin_gas_calc.
