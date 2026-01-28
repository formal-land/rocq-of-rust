Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.cmp.
Require Import core.simulate.cmp.
Require Import revm.revm_interpreter.instructions.links.i256.
Require Import ruint.links.lib.
Require Import ruint.simulate.cmp.

(*
pub fn i256_sign(val: &U256) -> Sign {
    if val.bit(U256::BITS - 1) {
        Sign::Minus
    } else {
        // SAFETY: false == 0 == Zero, true == 1 == Plus
        unsafe { core::mem::transmute::<bool, Sign>(!val.is_zero()) }
    }
}
*)
Definition i256_sign (val : aliases.U256.t) : Sign.t :=
  let high_bit := Z.testbit val.(Uint.value) 255 in
  if high_bit then
    Sign.Minus
  else if val.(Uint.value) =? 0 then
    Sign.Zero
  else
    Sign.Plus.

Lemma i256_sign_eq
    (stack : Stack.t)
    (ref_val : '& aliases.U256.t)
    (val : aliases.U256.t) :
  CanRead.t stack val ref_val ->
  {{
    SimulateM.eval_f
      (run_i256_sign ref_val)
      stack 🌲
    (
      Output.Success (i256_sign val),
      stack
    )
  }}.
Admitted.

Module Impl_Ord_for_Sign.
  Definition cmp (s1 s2 : Sign.t) : Ordering.t :=
    match s1, s2 with
    | Sign.Minus, Sign.Minus => Ordering.Equal
    | Sign.Minus, _ => Ordering.Less
    | Sign.Zero, Sign.Minus => Ordering.Greater
    | Sign.Zero, Sign.Zero => Ordering.Equal
    | Sign.Zero, Sign.Plus => Ordering.Less
    | Sign.Plus, Sign.Plus => Ordering.Equal
    | Sign.Plus, _ => Ordering.Greater
    end.
End Impl_Ord_for_Sign.

(*
pub fn i256_cmp(first: &U256, second: &U256) -> Ordering {
    let first_sign = i256_sign(first);
    let second_sign = i256_sign(second);
    match first_sign.cmp(&second_sign) {
        // Note: Adding `if first_sign != Sign::Zero` to short circuit zero comparisons performs
        // slower on average, as of #582
        Ordering::Equal => first.cmp(second),
        o => o,
    }
}
*)
Definition i256_cmp (first second : aliases.U256.t) : Ordering.t :=
  let first_sign := i256_sign first in
  let second_sign := i256_sign second in
  match Impl_Ord_for_Sign.cmp first_sign second_sign with
  | Ordering.Equal => Impl_Ord_for_Uint.cmp first second
  | o => o
  end.

Lemma i256_cmp_eq
    (stack : Stack.t)
    (ref_first ref_second : '& aliases.U256.t)
    (first second : aliases.U256.t) :
  CanRead.t stack first ref_first ->
  CanRead.t stack second ref_second ->
  {{
    SimulateM.eval_f
      (run_i256_cmp ref_first ref_second)
      stack 🌲
    (
      Output.Success (i256_cmp first second),
      stack
    )
  }}.
Admitted.
