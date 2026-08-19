Require Import simulate.RocqOfRust.
Require Import core.convert.links.mod.
Require Import core.links.option.
Require Import core.links.result.
Require Import core.ops.links.control_flow.
Require Import core.ops.links.try_trait.
Require Import core.ops.simulate.function.
Require Import core.ops.simulate.try_trait.
Require Import core.simulate.default.

Module Impl_Option.
  Definition Self (T : Set) : Set := option T.

  Definition map {T U F : Set}
      `{FnOnce.C F T U}
      (self : Self T) (f : F) : option U :=
    match self with
    | Some value => Some (FnOnce.call_once f value)
    | None => None
    end.

  Lemma map_eq
      {T U F : Set} `{Link T} `{Link U} `{Link F}
      (Run_FnOnce_for_F : function.FnOnce.Run F T U)
      `{IFnOnce : FnOnce.C F T U}
      `{!FnOnce.Eq.C IFnOnce}
    (self : Self T) (f : F) (stack : Stack.t) :
    {{
      SimulateM.eval_f (Impl_Option.run_map Run_FnOnce_for_F self f) stack 🌲
      (Output.Success (map self f), stack)
    }}.
  Proof.
  Admitted.

  Definition ok_or {T E : Set} (self : Self T) (err : E) : Result.t T E :=
    match self with
    | Some value => Result.Ok value
    | None => Result.Err err
    end.

  Lemma ok_or_eq
      {T E : Set} `{Link T} `{Link E}
      (self : Self T) (err : E) (stack : Stack.t) :
    {{
      SimulateM.eval_f (Impl_Option.run_ok_or self err) stack 🌲
      (Output.Success (ok_or self err), stack)
    }}.
  Proof.
    destruct self; s.
  Qed.

  Lemma unwrap_eq {T : Set} `{Link T} (stack : Stack.t) (self : Self T) (value : T) :
    self = Some value ->
    {{
      SimulateM.eval_f (Impl_Option.run_unwrap self) stack 🌲
      (Output.Success value, stack)
    }}.
  Proof.
    intros.
    subst.
    s.
  Qed.

  Lemma unwrap_unchecked_eq {T : Set} `{Link T} (stack : Stack.t) (self : Self T) (value : T) :
    self = Some value ->
    {{
      SimulateM.eval_f (Impl_Option.run_unwrap_unchecked self) stack 🌲
      (Output.Success value, stack)
    }}.
  Proof.
    intros.
    subst.
    s.
  Qed.

  Definition unwrap_or_default
      {T : Set} `{Default.C T}
      (self : Self T) : T :=
    match self with
    | Some value => value
    | None => Default.default
    end.

  Lemma unwrap_or_default_eq
      {T : Set} `{Link T}
      `{!default.Default.Run T}
      `{Default_for_T : Default.C T}
      `{!Default.Eq.C (Self := T) Default_for_T}
      (stack : Stack.t) (self : Self T) :
    {{
      SimulateM.eval_f (Impl_Option.run_unwrap_or_default self) stack 🌲
      (Output.Success (unwrap_or_default self), stack)
    }}.
  Proof.
    destruct self; cbn.
    { s. }
    { s. {
        apply Default.Eq.default.
      }
      s.
    }
  Qed.

  (* pub fn unwrap_or(self, default: T) -> T *)
  Definition unwrap_or {T : Set} (self : Self T) (default : T) : T :=
    match self with
    | Some v => v
    | None => default
    end.

  Lemma unwrap_or_eq (stack : Stack.t)
      {T : Set} `{Link T} (self : Self T) (default : T) :
    {{
      SimulateM.eval_f
        (Impl_Option.run_unwrap_or self default)
        stack 🌲
      (
        Output.Success (unwrap_or self default),
        stack
      )
    }}.
  Proof.
    destruct self; s.
  Qed.

  Lemma expect_eq {T : Set} `{Link T}
      (stack : Stack.t) (self : Self T) (msg : '& string) (value : T) :
    self = Some value ->
    {{
      SimulateM.eval_f (Impl_Option.run_expect self msg) stack 🌲
      (Output.Success value, stack)
    }}.
  Proof.
    intros.
    subst.
    s.
  Qed.
End Impl_Option.
Export (hints) Impl_Option.

Module Impl_Try_for_Option.
  Definition Self (T : Set) : Set :=
    option T.

  Definition Types (T : Set) : Try.Types.t := {|
    Try.Types.Output := T;
    Try.Types.Residual := option Infallible.t;
  |}.

  Instance AreLinks (T : Set) `{Link T} : Try.Types.AreLinks (Types T).
  Proof.
    constructor; typeclasses eauto.
  Defined.

  Definition from_output {T : Set} (output : T) : Self T :=
    Some output.

  Lemma from_output_eq {T : Set} `{Link T}
      (output : T) (stack : Stack.t) :
    {{
      SimulateM.eval_f
        (Try.run_from_output (Self := Self T) (types := Types T) output)
        stack 🌲
      (Output.Success (from_output output), stack)
    }}.
  Proof.
  Admitted.

  Definition branch {T : Set} (self : Self T) :
      control_flow.ControlFlow.t (option Infallible.t) T :=
    match self with
    | Some value => control_flow.ControlFlow.Continue value
    | None => control_flow.ControlFlow.Break None
    end.

  Lemma branch_eq {T : Set} `{Link T}
      (self : Self T) (stack : Stack.t) :
    {{
      SimulateM.eval_f
        (Try.run_branch (Self := Self T) (types := Types T) self)
        stack 🌲
      (Output.Success (branch self), stack)
    }}.
  Proof.
  Admitted.

  Instance I (T : Set) `{Link T}
      `{HFromResidual : FromResidual.C (Self T) (Types T).(Try.Types.Residual)} :
      Try.C (Self T) (Types T) := {|
    Try.FromResidual_for_Self := HFromResidual;
    Try.from_output := from_output;
    Try.branch := branch;
  |}.

  Module Eq.
    Instance I (T : Set) `{Link T}
        `{HFromResidual : FromResidual.C (Self T) (Types T).(Try.Types.Residual)}
        `{!FromResidual.Eq.C HFromResidual} :
        Try.Eq.C (Impl_Try_for_Option.I T).
    Proof.
    Admitted.
  End Eq.
  Export (hints) Eq.
End Impl_Try_for_Option.
Export (hints) Impl_Try_for_Option.

Module Impl_FromResidual_Infallible_for_Option.
  Definition Self (T : Set) : Set :=
    option T.

  Definition from_residual {T : Set} (residual : option Infallible.t) : Self T :=
    match residual with
    | None => None
    | Some impossible =>
      match impossible with
      end
    end.

  Lemma from_residual_eq {T : Set} `{Link T}
      (residual : option Infallible.t) (stack : Stack.t) :
    {{
      SimulateM.eval_f
        (FromResidual.run_from_residual (Self := Self T) (R := option Infallible.t) residual)
        stack 🌲
      (Output.Success (from_residual residual), stack)
    }}.
  Proof.
  Admitted.

  Instance I (T : Set) :
      FromResidual.C (Self T) (option Infallible.t) := {|
    FromResidual.from_residual := from_residual;
  |}.

  Module Eq.
    Instance I (T : Set) `{Link T} :
      FromResidual.Eq.C
        (Self := Self T)
        (R := option Infallible.t)
        (Impl_FromResidual_Infallible_for_Option.I T).
    Proof.
      constructor.
      apply from_residual_eq.
    Qed.
  End Eq.
  Export (hints) Eq.
End Impl_FromResidual_Infallible_for_Option.
Export (hints) Impl_FromResidual_Infallible_for_Option.
