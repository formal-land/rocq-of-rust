Require Import simulate.RocqOfRust.
Require Import core.ops.links.control_flow.
Require Import core.ops.links.try_trait.

Module FromResidual.
  Class C (Self : Set) (R : Set) : Set := {
    from_residual (residual : R) : Self;
  }.

  Module Eq.
    Class C
        {Self : Set} `{Link Self}
        {R : Set} `{Link R}
        `{!try_trait.FromResidual.Run Self R}
        `(!FromResidual.C Self R) :
        Prop := {
      from_residual (residual : R) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (try_trait.FromResidual.run_from_residual residual)
            stack 🌲
          (
            Output.Success (from_residual residual),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End FromResidual.
Export (hints) FromResidual.

Module Try.
  Class C
      (Self : Set) `{Link Self}
      (types : try_trait.Try.Types.t) `{try_trait.Try.Types.AreLinks types} :
      Set := {
    FromResidual_for_Self :: FromResidual.C Self types.(try_trait.Try.Types.Residual);
    from_output (output : types.(try_trait.Try.Types.Output)) : Self;
    branch (self : Self) :
      control_flow.ControlFlow.t
        types.(try_trait.Try.Types.Residual)
        types.(try_trait.Try.Types.Output);
  }.

  Module Eq.
    Class C
        {Self : Set} `{Link Self}
        {types : try_trait.Try.Types.t} `{try_trait.Try.Types.AreLinks types}
        `{!try_trait.Try.Run Self types}
        (I : Try.C Self types) :
        Prop := {
      FromResidual_for_Self :: FromResidual.Eq.C I.(FromResidual_for_Self);
      from_output
          (output : types.(try_trait.Try.Types.Output))
          (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (try_trait.Try.run_from_output output)
            stack 🌲
          (
            Output.Success (I.(Try.from_output) output),
            stack
          )
        }};
      branch
          (self : Self)
          (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (try_trait.Try.run_branch self)
            stack 🌲
          (
            Output.Success (I.(Try.branch) self),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End Try.
Export (hints) Try.

