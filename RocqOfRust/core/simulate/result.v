Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import core.links.result.

Module Impl_Result_T_E.
  Definition Self (T E : Set) : Set :=
    Result.t T E.

  Definition unwrap_or {T E : Set} (self : Self T E) (default : T) : T :=
    match self with
    | Result.Ok x => x
    | Result.Err _ => default
    end.

  Lemma unwrap_or_eq {T E : Set} `{Link T} `{Link E} (stack : Stack.t)
      (self : Self T E) (default : T) :
    {{
      SimulateM.eval_f (
        result.Impl_Result_T_E.run_unwrap_or T E self default
      )
      stack 🌲
      (
        Output.Success (unwrap_or self default),
        stack
      )
    }}.
  Proof.
    unfold run_unwrap_or; cbn.
    destruct self; cbn; apply Run.Pure.
  Qed.
  Global Opaque run_unwrap_or.
End Impl_Result_T_E.
