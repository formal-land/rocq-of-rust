Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.cmp.
Require Import core.simulate.cmp.
Require Import revm.revm_interpreter.instructions.links.i256.
Require Import ruint.links.lib.
Require Import ruint.simulate.add.
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
Proof.
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
Proof.
Admitted.

Definition sign_eqb (s1 s2 : Sign.t) : bool :=
  match s1, s2 with
  | Sign.Minus, Sign.Minus => true
  | Sign.Zero, Sign.Zero => true
  | Sign.Plus, Sign.Plus => true
  | _, _ => false
  end.

Definition two_compl (op : aliases.U256.t) : aliases.U256.t :=
  Impl_Uint.wrapping_sub
    {| Uint.value := 0 |}
    op.

Definition i256_sign_compl (val : aliases.U256.t) : Sign.t * aliases.U256.t :=
  let sign := i256_sign val in
  if sign_eqb sign Sign.Minus then
    (sign, two_compl val)
  else
    (sign, val).

Definition u256_remove_sign (val : aliases.U256.t) : aliases.U256.t :=
  {| Uint.value := Z.land val.(Uint.value) (2 ^ 255 - 1) |}.

Definition MIN_NEGATIVE_VALUE : aliases.U256.t :=
  {| Uint.value := 2 ^ 255 |}.

(*
pub fn i256_div(mut first: U256, mut second: U256) -> U256 {
    let second_sign = i256_sign_compl(&mut second);
    if second_sign == Sign::Zero {
        return U256::ZERO;
    }
    let first_sign = i256_sign_compl(&mut first);
    if first == MIN_NEGATIVE_VALUE && second == U256::from(1) {
        return two_compl(MIN_NEGATIVE_VALUE);
    }
    let mut d = first / second;
    u256_remove_sign(&mut d);
    if (first_sign == Sign::Minus && second_sign != Sign::Minus)
        || (second_sign == Sign::Minus && first_sign != Sign::Minus)
    {
        two_compl(d)
    } else {
        d
    }
}
*)
Definition i256_div (first second : aliases.U256.t) : aliases.U256.t :=
  let '(second_sign, second) := i256_sign_compl second in
  if sign_eqb second_sign Sign.Zero then
    {| Uint.value := 0 |}
  else
    let '(first_sign, first) := i256_sign_compl first in
    if (first.(Uint.value) =? MIN_NEGATIVE_VALUE.(Uint.value)) &&
       (second.(Uint.value) =? 1) then
      two_compl MIN_NEGATIVE_VALUE
    else
      let d := {| Uint.value := first.(Uint.value) / second.(Uint.value) |} in
      let d := u256_remove_sign d in
      if (sign_eqb first_sign Sign.Minus && negb (sign_eqb second_sign Sign.Minus)) ||
         (sign_eqb second_sign Sign.Minus && negb (sign_eqb first_sign Sign.Minus)) then
        two_compl d
      else
        d.

Lemma i256_div_eq
    (stack : Stack.t)
    (first second : aliases.U256.t) :
  {{
    SimulateM.eval_f
      (run_i256_div first second)
      stack 🌲
    (
      Output.Success (i256_div first second),
      stack
    )
  }}.
Proof.
Admitted.

(*
pub fn i256_mod(mut first: U256, mut second: U256) -> U256 {
    let first_sign = i256_sign_compl(&mut first);
    if first_sign == Sign::Zero {
        return U256::ZERO;
    }
    let second_sign = i256_sign_compl(&mut second);
    if second_sign == Sign::Zero {
        return U256::ZERO;
    }
    let mut r = first % second;
    u256_remove_sign(&mut r);
    if first_sign == Sign::Minus {
        two_compl(r)
    } else {
        r
    }
}
*)
Definition i256_mod (first second : aliases.U256.t) : aliases.U256.t :=
  let '(first_sign, first) := i256_sign_compl first in
  if sign_eqb first_sign Sign.Zero then
    {| Uint.value := 0 |}
  else
    let '(second_sign, second) := i256_sign_compl second in
    if sign_eqb second_sign Sign.Zero then
      {| Uint.value := 0 |}
    else
      let r := {| Uint.value := first.(Uint.value) mod second.(Uint.value) |} in
      let r := u256_remove_sign r in
      if sign_eqb first_sign Sign.Minus then
        two_compl r
      else
        r.

Lemma i256_mod_eq
    (stack : Stack.t)
    (first second : aliases.U256.t) :
  {{
    SimulateM.eval_f
      (run_i256_mod first second)
      stack 🌲
    (
      Output.Success (i256_mod first second),
      stack
    )
  }}.
Proof.
Admitted.
