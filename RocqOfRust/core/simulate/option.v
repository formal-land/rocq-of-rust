Require Import simulate.RocqOfRust.
Require Import core.links.option.

Module Impl_Option.
  Definition Self (T : Set) : Set := option T.

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
  Admitted.
End Impl_Option.
