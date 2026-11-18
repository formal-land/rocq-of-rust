Require Import RocqOfRust.simulate.RocqOfRust RocqOfRust.core.links.option.
Require Import RocqOfRust.core.ops.simulate.function.
Require Import RocqOfRust.core.simulate.option.

Section Map.
  Context {F T U : Set} `{Link F} `{Link T} `{Link U}
    (R : function.FnOnce.Run F (OneElementTuple.t T) U)
    (S : FnOnce.C F (OneElementTuple.t T) U)
    (HS : @FnOnce.Eq.C F (OneElementTuple.t T) U _ _ _ R S)
    (f : F) (stack : Stack.t).

  Example map_some (x : T) :
    {{ SimulateM.eval_f (Impl_Option.run_map R (Some x) f) stack 🌲
       (Output.Success (Some (S.(FnOnce.call_once) f {| OneElementTuple.value := x |})), stack) }}.
  Proof.
    apply (Impl_Option.map_eq R S HS (Some x) f stack). discriminate.
  Qed.

  Example map_none (unused : Impl_Option.callback_has_trivial_drop (Φ F) (φ f)) :
    {{ SimulateM.eval_f (Impl_Option.run_map R None f) stack 🌲
       (Output.Success None, stack) }}.
  Proof.
    apply (Impl_Option.map_eq R S HS None f stack). intros _. exact unused.
  Qed.
End Map.
