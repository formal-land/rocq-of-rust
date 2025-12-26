Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import core.links.result.
Require Import ruint.links.from.

Module TryFrom_Uint_for_u64.
  Definition Self : Set :=
    U64.t.

  Parameter try_from :
    forall {BITS LIMBS : Usize.t},
    Impl_Uint.Self BITS LIMBS ->
    Result.t Self (FromUintError.t U64.t).

  Lemma try_from_eq (BITS LIMBS : Usize.t) (value : Impl_Uint.Self BITS LIMBS) (stack : Stack.t) :
    {{
      SimulateM.eval_f
        (TryFrom_Uint_for_u64.run_try_from BITS LIMBS value)
        stack 🌲
      (
        Output.Success (try_from value),
        stack
      )
    }}.
  Admitted.
  Global Opaque TryFrom_Uint_for_u64.run_try_from.
End TryFrom_Uint_for_u64.
