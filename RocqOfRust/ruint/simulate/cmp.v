Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import ruint.links.cmp.
Require Import ruint.links.lib.

Module Impl_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  Parameter is_zero :
    forall {BITS LIMBS : usize} (self : Self BITS LIMBS),
    bool.

  Lemma is_zero_like {BITS LIMBS : usize}
      (stack : Stack.t)
      (ref_self : '& (Self BITS LIMBS)) :
    SimulateM.eval_f
      (Impl_Uint.run_is_zero BITS LIMBS ref_self)
      stack =
    let*s self := SimulateM.read stack ref_self.(Ref.core) in
    match self with
    | Output.Success value =>
      SimulateM.Pure (Output.Success (is_zero value), stack)
    | Output.Exception exception =>
      SimulateM.Pure (Output.Exception exception, stack)
    end.
  Admitted.
End Impl_Uint.
