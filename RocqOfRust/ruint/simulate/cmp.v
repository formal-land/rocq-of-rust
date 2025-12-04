Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import ruint.links.cmp.

Module Impl_Uint.
  Parameter is_zero :
    forall {BITS LIMBS : Usize.t} (self : Self BITS LIMBS),
    bool.

  Lemma is_zero_like {Stack : Stack.t} {BITS LIMBS : Usize.t}
      (stack : Stack.to_Set Stack)
      (ref_self : Ref.t Pointer.Kind.Ref (Self BITS LIMBS)) :
    SimulateM.eval_f (Stack := Stack)
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
