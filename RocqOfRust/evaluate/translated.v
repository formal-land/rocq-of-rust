Require Import RocqOfRust.RocqOfRust.

Module Translated.
  Module Execution.
    Inductive t : Set :=
    | Done (output : Value.t + Exception.t)
    | OutOfFuel
    | Unsupported (message : string).
  End Execution.

  Module Runtime.
    Record t : Set := {
      get_function :
        string ->
        list Value.t ->
        list Ty.t ->
        option PolymorphicFunction.t;
    }.

    Definition empty : t :=
      {| get_function := fun _ _ _ => None |}.
  End Runtime.

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

    Definition get_immediate_sub_pointer
        (pointer : Value.t)
        (index : Pointer.Index.t) :
        option Value.t :=
      match read_immediate pointer with
      | Some value =>
        match Value.read_index value index with
        | Some value => Some (immediate_pointer value)
        | None => None
        end
      | None => None
      end.

    Fixpoint eval
        (runtime : Runtime.t)
        (fuel : nat)
        (expression : M) :
        Execution.t :=
      match fuel with
      | O => Execution.OutOfFuel
      | S fuel =>
        match expression with
        | LowM.Pure output => Execution.Done output
        | LowM.CallPrimitive primitive k =>
          match primitive with
          | Primitive.StateAlloc _ value =>
            eval runtime fuel (k (immediate_pointer value))
          | Primitive.StateRead pointer =>
            match read_immediate pointer with
            | Some value => eval runtime fuel (k value)
            | None => Execution.Unsupported "unable to read pointer"
            end
          | Primitive.StateWrite _ _ =>
            Execution.Unsupported "state write"
          | Primitive.GetSubPointer pointer index =>
            match get_immediate_sub_pointer pointer index with
            | Some pointer => eval runtime fuel (k pointer)
            | None => Execution.Unsupported "unable to get sub-pointer"
            end
          | Primitive.GetFunction path generic_consts generic_tys =>
            match runtime.(Runtime.get_function) path generic_consts generic_tys with
            | Some function =>
              eval runtime fuel (k (M.closure (function generic_consts generic_tys)))
            | None => Execution.Unsupported "function not found"
            end
          | Primitive.GetAssociatedFunction _ _ _ _ =>
            Execution.Unsupported "associated function resolution"
          | Primitive.GetTraitMethod _ _ _ _ _ _ _ =>
            Execution.Unsupported "trait method resolution"
          end
        | LowM.CallClosure _ closure arguments k =>
          match closure_body closure with
          | Some body =>
            match eval runtime fuel (body arguments) with
            | Execution.Done output => eval runtime fuel (k output)
            | Execution.OutOfFuel => Execution.OutOfFuel
            | Execution.Unsupported message => Execution.Unsupported message
            end
          | None => Execution.Unsupported "value is not a closure"
          end
        | LowM.CallLogicalOp _ _ _ _ =>
          Execution.Unsupported "logical operator"
        | LowM.Let _ expression k =>
          match eval runtime fuel expression with
          | Execution.Done output => eval runtime fuel (k output)
          | Execution.OutOfFuel => Execution.OutOfFuel
          | Execution.Unsupported message => Execution.Unsupported message
          end
        | LowM.LetAlloc _ expression k =>
          match eval runtime fuel expression with
          | Execution.Done (inl value) =>
            eval runtime fuel (k (inl (immediate_pointer value)))
          | Execution.Done (inr exception) =>
            eval runtime fuel (k (inr exception))
          | Execution.OutOfFuel => Execution.OutOfFuel
          | Execution.Unsupported message => Execution.Unsupported message
          end
        | LowM.Loop _ _ _ => Execution.Unsupported "loop"
        | LowM.MatchTuple tuple k =>
          match tuple with
          | Value.Tuple fields => eval runtime fuel (k fields)
          | _ => Execution.Unsupported "expected a tuple"
          end
        | LowM.IfThenElse _ condition then_ else_ k =>
          match condition with
          | Value.Bool true =>
            match eval runtime fuel then_ with
            | Execution.Done output => eval runtime fuel (k output)
            | Execution.OutOfFuel => Execution.OutOfFuel
            | Execution.Unsupported message => Execution.Unsupported message
            end
          | Value.Bool false =>
            match eval runtime fuel else_ with
            | Execution.Done output => eval runtime fuel (k output)
            | Execution.OutOfFuel => Execution.OutOfFuel
            | Execution.Unsupported message => Execution.Unsupported message
            end
          | _ => Execution.Unsupported "expected a boolean condition"
          end
        | LowM.Impossible _ => Execution.Unsupported "impossible"
        end
      end.
  End Evaluate.
End Translated.
