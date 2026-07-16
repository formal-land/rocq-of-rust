Require Import RocqOfRust.RocqOfRust.

Module Translated.
  Parameter ty_eqb : Ty.t -> Ty.t -> bool.

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
      get_trait_method :
        string ->
        Ty.t ->
        list Value.t ->
        list Ty.t ->
        string ->
        list Value.t ->
        list Ty.t ->
        option PolymorphicFunction.t;
    }.

    Definition empty : t :=
      {|
        get_function := fun _ _ _ => None;
        get_trait_method := fun _ _ _ _ _ _ _ => None;
      |}.

    Fixpoint find_trait_method
        (methods :
          list
            (string *
              list Ty.t *
              Ty.t *
              string *
              PolymorphicFunction.t))
        (trait_name : string)
        (trait_tys : list Ty.t)
        (self_ty : Ty.t)
        (method_name : string) :
        option PolymorphicFunction.t :=
      match methods with
      | [] => None
      | (entry_trait_name,
          entry_trait_tys,
          entry_self_ty,
          entry_method_name,
          method) :: methods =>
        match PrimString.compare entry_trait_name trait_name with
        | Eq =>
          if List.eqb ty_eqb entry_trait_tys trait_tys then
            if ty_eqb entry_self_ty self_ty then
              match PrimString.compare entry_method_name method_name with
              | Eq => Some method
              | _ => find_trait_method methods trait_name trait_tys self_ty method_name
              end
            else find_trait_method methods trait_name trait_tys self_ty method_name
          else find_trait_method methods trait_name trait_tys self_ty method_name
        | _ => find_trait_method methods trait_name trait_tys self_ty method_name
        end
      end.

    Definition of_tables
        (functions : list (string * PolymorphicFunction.t))
        (trait_methods :
          list
            (string *
              list Ty.t *
              Ty.t *
              string *
              PolymorphicFunction.t)) :
        t :=
      {|
        get_function := fun path _ _ => List.assoc functions path;
        get_trait_method :=
          fun trait_name self_ty trait_consts trait_tys method_name _ _ =>
            match trait_consts with
            | [] =>
              find_trait_method
                trait_methods
                trait_name
                trait_tys
                self_ty
                method_name
            | _ => None
            end;
      |}.

    Definition of_function_table
        (functions : list (string * PolymorphicFunction.t)) :
        t :=
      of_tables functions [].
  End Runtime.

  Module Memory.
    Definition t : Set := list Value.t.

    Definition empty : t := [].

    Parameter address_to_nat : forall {Address : Set}, Address -> option nat.

    Definition make_pointer (address : nat) (path : Pointer.Path.t) : Value.t :=
      Value.Pointer {|
        Pointer.kind := Pointer.Kind.Ref;
        Pointer.core := Pointer.Core.Mutable address path;
      |}.

    Fixpoint read_path (value : Value.t) (path : Pointer.Path.t) : option Value.t :=
      match path with
      | [] => Some value
      | index :: path =>
        match Value.read_index value index with
        | Some value => read_path value path
        | None => None
        end
      end.

    Fixpoint write_path
        (value : Value.t)
        (path : Pointer.Path.t)
        (update : Value.t) :
        option Value.t :=
      match path with
      | [] => Some update
      | index :: path =>
        match Value.read_index value index with
        | Some sub_value =>
          match write_path sub_value path update with
          | Some sub_update => Value.write_index value index sub_update
          | None => None
          end
        | None => None
        end
      end.

    Definition alloc (memory : t) (value : Value.t) : Value.t * t :=
      (make_pointer (List.length memory) [], memory ++ [value]).

    Definition read (memory : t) (pointer : Value.t) : option Value.t :=
      match pointer with
      | Value.Pointer pointer =>
        match pointer.(Pointer.core) with
        | Pointer.Core.Immediate value => value
        | Pointer.Core.Mutable address path =>
          match address_to_nat address with
          | Some address =>
            match List.nth_error memory address with
            | Some value => read_path value path
            | None => None
            end
          | None => None
          end
        end
      | _ => None
      end.

    Definition write
        (memory : t)
        (pointer update : Value.t) :
        option t :=
      match pointer with
      | Value.Pointer pointer =>
        match pointer.(Pointer.core) with
        | Pointer.Core.Immediate _ => None
        | Pointer.Core.Mutable address path =>
          match address_to_nat address with
          | Some address =>
            match List.nth_error memory address with
            | Some value =>
              match write_path value path update with
              | Some value => Some (List.replace_at memory address value)
              | None => None
              end
            | None => None
            end
          | None => None
          end
        end
      | _ => None
      end.

    Definition get_sub_pointer
        (memory : t)
        (pointer : Value.t)
        (index : Pointer.Index.t) :
        option Value.t :=
      match pointer with
      | Value.Pointer pointer =>
        match pointer.(Pointer.core) with
        | Pointer.Core.Immediate value =>
          match value with
          | Some value =>
            match Value.read_index value index with
            | Some value =>
              Some (Value.Pointer {|
                Pointer.kind := pointer.(Pointer.kind);
                Pointer.core := Pointer.Core.Immediate (Some value);
              |})
            | None => None
            end
          | None => None
          end
        | Pointer.Core.Mutable address path =>
          match read memory (Value.Pointer pointer) with
          | Some value =>
            match Value.read_index value index with
            | Some _ =>
              Some (Value.Pointer {|
                Pointer.kind := pointer.(Pointer.kind);
                Pointer.core := Pointer.Core.Mutable address (path ++ [index]);
              |})
            | None => None
            end
          | None => None
          end
        end
      | _ => None
      end.
  End Memory.

  Module Evaluate.
    Parameter closure_body : Value.t -> option (list Value.t -> M).

    Module Result.
      Inductive t : Set :=
      | Done (output : Value.t + Exception.t) (memory : Memory.t)
      | OutOfFuel
      | Unsupported (message : string).
    End Result.

    Fixpoint eval_with_memory
        (runtime : Runtime.t)
        (fuel : nat)
        (memory : Memory.t)
        (expression : M) :
        Result.t :=
      match fuel with
      | O => Result.OutOfFuel
      | S fuel =>
        match expression with
        | LowM.Pure output => Result.Done output memory
        | LowM.CallPrimitive primitive k =>
          match primitive with
          | Primitive.StateAlloc _ value =>
            let '(pointer, memory) := Memory.alloc memory value in
            eval_with_memory runtime fuel memory (k pointer)
          | Primitive.StateRead pointer =>
            match Memory.read memory pointer with
            | Some value => eval_with_memory runtime fuel memory (k value)
            | None => Result.Unsupported "unable to read pointer"
            end
          | Primitive.StateWrite pointer update =>
            match Memory.write memory pointer update with
            | Some memory =>
              eval_with_memory runtime fuel memory (k (Value.Tuple []))
            | None => Result.Unsupported "unable to write pointer"
            end
          | Primitive.GetSubPointer pointer index =>
            match Memory.get_sub_pointer memory pointer index with
            | Some pointer => eval_with_memory runtime fuel memory (k pointer)
            | None => Result.Unsupported "unable to get sub-pointer"
            end
          | Primitive.GetFunction path generic_consts generic_tys =>
            match runtime.(Runtime.get_function) path generic_consts generic_tys with
            | Some function =>
              eval_with_memory
                runtime
                fuel
                memory
                (k (M.closure (function generic_consts generic_tys)))
            | None => Result.Unsupported "function not found"
            end
          | Primitive.GetAssociatedFunction _ _ _ _ =>
            Result.Unsupported "associated function resolution"
          | Primitive.GetTraitMethod
              trait_name self_ty trait_consts trait_tys method_name generic_consts generic_tys =>
            match runtime.(Runtime.get_trait_method)
              trait_name
              self_ty
              trait_consts
              trait_tys
              method_name
              generic_consts
              generic_tys with
            | Some method =>
              eval_with_memory
                runtime
                fuel
                memory
                (k (M.closure (method generic_consts generic_tys)))
            | None => Result.Unsupported "trait method not found"
            end
          end
        | LowM.CallClosure _ closure arguments k =>
          match closure_body closure with
          | Some body =>
            match eval_with_memory runtime fuel memory (body arguments) with
            | Result.Done output memory =>
              eval_with_memory runtime fuel memory (k output)
            | Result.OutOfFuel => Result.OutOfFuel
            | Result.Unsupported message => Result.Unsupported message
            end
          | None => Result.Unsupported "value is not a closure"
          end
        | LowM.CallLogicalOp _ _ _ _ =>
          Result.Unsupported "logical operator"
        | LowM.Let _ expression k =>
          match eval_with_memory runtime fuel memory expression with
          | Result.Done output memory =>
            eval_with_memory runtime fuel memory (k output)
          | Result.OutOfFuel => Result.OutOfFuel
          | Result.Unsupported message => Result.Unsupported message
          end
        | LowM.LetAlloc _ expression k =>
          match eval_with_memory runtime fuel memory expression with
          | Result.Done (inl value) memory =>
            let '(pointer, memory) := Memory.alloc memory value in
            eval_with_memory runtime fuel memory (k (inl pointer))
          | Result.Done (inr exception) memory =>
            eval_with_memory runtime fuel memory (k (inr exception))
          | Result.OutOfFuel => Result.OutOfFuel
          | Result.Unsupported message => Result.Unsupported message
          end
        | LowM.Loop _ _ _ => Result.Unsupported "loop"
        | LowM.MatchTuple tuple k =>
          match tuple with
          | Value.Tuple fields => eval_with_memory runtime fuel memory (k fields)
          | _ => Result.Unsupported "expected a tuple"
          end
        | LowM.IfThenElse _ condition then_ else_ k =>
          match condition with
          | Value.Bool true =>
            match eval_with_memory runtime fuel memory then_ with
            | Result.Done output memory =>
              eval_with_memory runtime fuel memory (k output)
            | Result.OutOfFuel => Result.OutOfFuel
            | Result.Unsupported message => Result.Unsupported message
            end
          | Value.Bool false =>
            match eval_with_memory runtime fuel memory else_ with
            | Result.Done output memory =>
              eval_with_memory runtime fuel memory (k output)
            | Result.OutOfFuel => Result.OutOfFuel
            | Result.Unsupported message => Result.Unsupported message
            end
          | _ => Result.Unsupported "expected a boolean condition"
          end
        | LowM.Impossible _ => Result.Unsupported "impossible"
        end
      end.

    Definition eval
        (runtime : Runtime.t)
        (fuel : nat)
        (expression : M) :
        Execution.t :=
      match eval_with_memory runtime fuel Memory.empty expression with
      | Result.Done output _ => Execution.Done output
      | Result.OutOfFuel => Execution.OutOfFuel
      | Result.Unsupported message => Execution.Unsupported message
      end.
  End Evaluate.
End Translated.
