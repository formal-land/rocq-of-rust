Require Import simulate.RocqOfRust.
Require Import core.ops.links.function.

Module FnOnce.
  Class C (Self Args Output : Set) : Set := {
    call_once (self : Self) (args : Args) : Output;
  }.

  Module Eq.
    Class C
        {Self Args Output : Set}
        `{Link Self} `{Link Args} `{Link Output}
        `{!function.FnOnce.Run Self Args Output}
        `(!FnOnce.C Self Args Output) :
        Prop := {
      call_once (self : Self) (args : Args) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (function.FnOnce.run_call_once self args)
            stack 🌲
          (
            Output.Success (call_once self args),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End FnOnce.
Export (hints) FnOnce.
