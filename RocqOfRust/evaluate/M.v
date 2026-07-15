Require Import simulate.RocqOfRust.

Module Execution.
  Inductive t (A : Set) : Set :=
  | Done (value : A)
  | OutOfFuel
  | Unsupported.
  Arguments Done {_}.
  Arguments OutOfFuel {_}.
  Arguments Unsupported {_}.
End Execution.

Module Evaluate.
  Fixpoint eval
      (fuel : nat)
      {R Output : Set}
      (e : LinkM.t R Output)
      (stack : Stack.t)
      {struct fuel} :
      Execution.t (Output.t R Output * Stack.t).
  Proof.
    destruct fuel as [|fuel].
    { exact Execution.OutOfFuel. }
    destruct e.
    { exact (Execution.Done (value, stack)). }
    { destruct primitive.
      { exact (@eval fuel R Output (k (Ref.Core.Immediate (Some value))) stack). }
      { destruct ref_core as [value|Address Big_A address path big_to_value projection injection].
        { destruct value as [value|].
          { exact (@eval fuel R Output (k value) stack). }
          { exact (Execution.Done (
              Output.Exception Output.Exception.BreakMatch,
              stack
            )).
          }
        }
        { (* Mutable references require access evidence for the heterogeneous stack. *)
          exact Execution.Unsupported.
        }
      }
      { exact Execution.Unsupported. }
      { exact (@eval fuel R Output (k (SubPointer.Runner.apply ref_core runner)) stack). }
    }
    { destruct (@eval fuel R A e stack) as [[output stack']| |].
      { exact (@eval fuel R Output (k output) stack'). }
      { exact Execution.OutOfFuel. }
      { exact Execution.Unsupported. }
    }
    { exact Execution.Unsupported. }
    { destruct (@eval fuel A A (links.M.evaluate run_f) stack) as [[output stack']| |].
      { destruct output as [value|exception].
        { exact (@eval fuel R Output (k value) stack'). }
        { exact Execution.Unsupported. }
      }
      { exact Execution.OutOfFuel. }
      { exact Execution.Unsupported. }
    }
    { exact Execution.Unsupported. }
    { exact (
        if cond then
          @eval fuel R Output e1 stack
        else
          @eval fuel R Output e2 stack
      ).
    }
    { destruct output as [value|exception].
      { exact (@eval fuel R Output (k_success value) stack). }
      { destruct exception.
        { exact (@eval fuel R Output (k_return return_) stack). }
        { exact (@eval fuel R Output (k_break tt) stack). }
        { exact (@eval fuel R Output (k_continue tt) stack). }
        { exact (@eval fuel R Output (k_break_match tt) stack). }
      }
    }
    { exact Execution.Unsupported. }
  Defined.

  Definition eval_f
      (fuel : nat)
      {f : PolymorphicFunction.t}
      {epsilon : list Value.t}
      {types : list Ty.t}
      {arguments : list Value.t}
      {Output : Set} `{Link Output}
      (run : Run.Trait f epsilon types arguments Output)
      (stack : Stack.t) :
      Execution.t (Output.t Output Output * Stack.t) :=
    @eval fuel Output Output (links.M.evaluate run.(Run.run_f)) stack.
End Evaluate.
