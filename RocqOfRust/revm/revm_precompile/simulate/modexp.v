Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_precompile.links.modexp.
Require Import ruint.links.lib.opam exec --switch=rocq90 -- make revm/revm_precompile/simulate/modexp.vo

(* Maximum value representable by u64. *)
Definition max_u64 : Z :=
  2 ^ 64 - 1.

(* Saturating addition and multiplication over non-negative integers. *)
Definition saturating_add_u64 (x y : Z) : Z :=
  Z.min max_u64 (x + y).

Definition saturating_mul_u64 (x y : Z) : Z :=
  Z.min max_u64 (x * y).

(* Number of bits required to represent a U256 value. *)
Definition bit_length (value : aliases.U256.t) : Z :=
  if value.(Uint.value) =? 0 then
    0
  else
    Z.log2 value.(Uint.value) + 1.

(* Functional specification of calculate_iteration_count. *)
Definition calculate_iteration_count
    (MULTIPLIER exp_length : u64)
    (exp_highp : aliases.U256.t) : u64 :=

  let multiplier := MULTIPLIER.(Integer.value) in
  let length := exp_length.(Integer.value) in
  let bits := bit_length exp_highp in

  let iteration_count :=
    if length <=? 32 then
      if exp_highp.(Uint.value) =? 0 then
        0
      else
        bits - 1
    else
      saturating_add_u64
        (saturating_mul_u64 multiplier (length - 32))
        (Z.max 1 bits - 1)
  in

  {| Integer.value := Z.max iteration_count 1 |}.

Module Test.

  Lemma calculate_iteration_count_zero :
    calculate_iteration_count
      {| Integer.value := 3 |}
      {| Integer.value := 10 |}
      {| Uint.value := 0 |}
    =
      {| Integer.value := 1 |}.
  Proof.
    reflexivity.
  Qed.

  Lemma calculate_iteration_count_short_nonzero :
    calculate_iteration_count
      {| Integer.value := 3 |}
      {| Integer.value := 10 |}
      {| Uint.value := 8 |}
    =
      {| Integer.value := 3 |}.
  Proof.
    reflexivity.
  Qed.

  Lemma calculate_iteration_count_long :
    calculate_iteration_count
      {| Integer.value := 3 |}
      {| Integer.value := 40 |}
      {| Uint.value := 8 |}
    =
      {| Integer.value := 27 |}.
  Proof.
    reflexivity.
  Qed.
End Test.
Lemma calculate_iteration_count_eq
    (stack : Stack.t)
    (MULTIPLIER exp_length : u64)
    (exp_highp : aliases.U256.t)
    (ref_exp_highp : '& aliases.U256.t) :
  CanRead.t stack exp_highp ref_exp_highp ->
  {{
    SimulateM.eval_f
      (run_calculate_iteration_count
        MULTIPLIER
        exp_length
        ref_exp_highp)
      stack 🌲
    (
      Output.Success
        (calculate_iteration_count
          MULTIPLIER
          exp_length
          exp_highp),
      stack
    )
  }}.
Proof.
Admitted.