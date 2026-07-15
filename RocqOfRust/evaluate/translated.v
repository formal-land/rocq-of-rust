Require Import RocqOfRust.RocqOfRust.

Module Translated.
  Module Execution.
    Inductive t : Set :=
    | Done (output : Value.t + Exception.t)
    | OutOfFuel
    | Unsupported.
  End Execution.

  Module Evaluate.
    Parameter closure_body : Value.t -> option (list Value.t -> M).

    Definition immediate_pointer (value : Value.t) : Value.t :=
      Value.Pointer {|
        Pointer.kind := Pointer.Kind.Ref;
        Pointer.core := Pointer.Core.Immediate (Some value);
      |}.

    Definition read_immediate (pointer : Value.t) : option Value.t :=
      match pointer with
      | Value.Pointer pointer =>
        match pointer.(Pointer.core) with
        | Pointer.Core.Immediate value => value
        | Pointer.Core.Mutable _ _ => None
        end
      | _ => None
      end.

    Fixpoint eval (fuel : nat) (expression : M) : Execution.t :=
      match fuel with
      | O => Execution.OutOfFuel
      | S fuel =>
        match expression with
        | LowM.Pure output => Execution.Done output
        | LowM.CallPrimitive primitive k =>
          match primitive with
          | Primitive.StateAlloc _ value =>
            eval fuel (k (immediate_pointer value))
          | Primitive.StateRead pointer =>
            match read_immediate pointer with
            | Some value => eval fuel (k value)
            | None => Execution.Unsupported
            end
          | _ => Execution.Unsupported
          end
        | LowM.CallClosure _ closure arguments k =>
          match closure_body closure with
          | Some body =>
            match eval fuel (body arguments) with
            | Execution.Done output => eval fuel (k output)
            | Execution.OutOfFuel => Execution.OutOfFuel
            | Execution.Unsupported => Execution.Unsupported
            end
          | None => Execution.Unsupported
          end
        | LowM.Let _ expression k =>
          match eval fuel expression with
          | Execution.Done output => eval fuel (k output)
          | Execution.OutOfFuel => Execution.OutOfFuel
          | Execution.Unsupported => Execution.Unsupported
          end
        | LowM.MatchTuple tuple k =>
          match tuple with
          | Value.Tuple fields => eval fuel (k fields)
          | _ => Execution.Unsupported
          end
        | LowM.IfThenElse _ condition then_ else_ k =>
          match condition with
          | Value.Bool true =>
            match eval fuel then_ with
            | Execution.Done output => eval fuel (k output)
            | Execution.OutOfFuel => Execution.OutOfFuel
            | Execution.Unsupported => Execution.Unsupported
            end
          | Value.Bool false =>
            match eval fuel else_ with
            | Execution.Done output => eval fuel (k output)
            | Execution.OutOfFuel => Execution.OutOfFuel
            | Execution.Unsupported => Execution.Unsupported
            end
          | _ => Execution.Unsupported
          end
        | _ => Execution.Unsupported
        end
      end.
  End Evaluate.
End Translated.
