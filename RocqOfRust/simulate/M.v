Require Import RocqOfRust.RocqOfRust.
Require Import links.M.

Module Stack.
  Inductive t : Set :=
  | Nil
  | Cons {A : Set} (value : A) (stack : t).

  Module Nth.
    Inductive t (A : Set) : Stack.t -> nat -> Set :=
    | ConsZero (value : A) (stack : Stack.t) :
      t A (Stack.Cons value stack) 0
    | ConsSucc {A' : Set} (value : A') (stack : Stack.t) (index : nat) :
      t A stack index ->
      t A (Stack.Cons value stack) (S index).
  End Nth.

  Fixpoint length (stack : t) : nat :=
    match stack with
    | Nil => 0
    | Cons _ stack => S (length stack)
    end.

  Fixpoint read
    {stack : t} {index : nat} {A : Set}
    (nth : Nth.t A stack index)
    {struct nth} :
    A.
  Proof.
    destruct nth.
    { exact value. }
    { exact (read _ _ _ nth). }
  Defined.

  Fixpoint write
    {stack : t} {index : nat} {A : Set}
    (nth : Nth.t A stack index)
    (new_value : A)
    {struct nth} :
    t.
  Proof.
    destruct nth.
    { exact (Cons new_value stack). }
    { exact (Cons value (write _ _ _ nth new_value)). }
  Defined.

  Fixpoint alloc {A : Set}
    (stack : t)
    (new_value : A)
    {struct stack} :
    t.
  Proof.
    destruct stack.
    { exact (Cons new_value Nil). }
    { exact (Cons value (alloc _ stack new_value)). }
  Defined.
  Arguments alloc _ _ /.

  Fixpoint dealloc (stack : t) {struct stack} : t :=
    match stack with
    | Nil => Nil
    | Cons _ Nil => Nil
    | Cons value stack => Cons value (dealloc stack)
    end.

  Declare Scope stack_scope.
  Delimit Scope stack_scope with stack.

  Notation "[ ]" := Nil (format "[ ]") : stack_scope.
  Notation "[ x ]" := (Cons x Nil) (format "[ x ]") : stack_scope.
  Notation "[ x ; y ; .. ; z ]" := (Cons x (Cons y .. (Cons z Nil) ..)) (format "[ x ; y ; .. ; z ]") : stack_scope.
  Notation "x :: y" := (Cons x y) (at level 60, right associativity) : stack_scope.

  Module CanAccess.
    Inductive t {A : Set} `{Link A} (stack : Stack.t) : Ref.Core.t A -> Set :=
    | Mutable
        (index : nat) (Big_A : Set)
        (nth : Nth.t Big_A stack index)
        (path : Pointer.Path.t)
        (big_to_value : Big_A -> Value.t)
        (projection : Big_A -> option A)
        (injection : Big_A -> A -> option Big_A) :
      t stack (Ref.Core.Mutable (Address := nat) (Big_A := Big_A)
        index path big_to_value projection injection
      ).

    Definition runner {stack : Stack.t} {A : Set} `{Link A} {index : Pointer.Index.t}
        {ref_core : Ref.Core.t A}
        (runner : SubPointer.Runner.t A index)
        (H_ref_core : t stack ref_core) :
      t stack (SubPointer.Runner.apply ref_core runner).
    Proof.
      destruct H_ref_core.
      apply Mutable.
      exact nth.
    Defined.

    Definition read {A : Set} `{Link A} {stack : Stack.t}
        {ref_core : Ref.Core.t A}
        (run : t stack ref_core) :
        option A :=
      match run with
      | Mutable _ _ _ nth _ _ projection _ => projection (read nth)
      end.

    Definition write {A : Set} `{Link A} {stack : Stack.t}
        {ref_core : Ref.Core.t A}
        (run : t stack ref_core)
        (value : A) :
        option Stack.t :=
      match run with
      | Mutable _ _ _ nth _ _ _ injection =>
        match injection (Stack.read nth) value with
        | Some value => Some (Stack.write nth value)
        | None => None
        end
      end.
  End CanAccess.
End Stack.
Export (notations) Stack.

(** Here we define an execution mode where we keep dynamic cast to retrieve data from the stack. In
    practice, these casts should always be correct as the original Rust code was well typed. *)
Module SimulateM.
  Inductive t (A : Set) : Set :=
  | Pure (value : A)
  | GetCanAccess {B : Set} `{Link B}
      (stack : Stack.t)
      (ref_core : Ref.Core.t B)
      (k : Stack.CanAccess.t stack ref_core -> t A)
  | Call {B : Set} `{Link B}
      {f : list Value.t -> M} {args : list Value.t}
      (stack_in : Stack.t)
      (run_f : {{ f args 🔽 B }})
      (k : B * Stack.t -> t A)
  | Impossible {T : Set} (payload : T).
  Arguments Pure {_}.
  Arguments GetCanAccess {_ _ _}.
  Arguments Call {_ _ _ _ _}.
  Arguments Impossible {_ _}.

  Fixpoint let_ {A B : Set} (e1 : t A) (e2 : A -> t B) : t B :=
    match e1 with
    | Pure value => e2 value
    | GetCanAccess Stack ref_core k =>
      GetCanAccess Stack ref_core (fun can_access => let_ (k can_access) e2)
    | Call stack_in run_f k => Call stack_in run_f (fun output_stack => let_ (k output_stack) e2)
    | Impossible payload => Impossible payload
    end.

  Notation "'let*s' x ':=' X 'in' Y" :=
    (let_ X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).

  Definition read {R : Set} {A : Set} `{Link A}
      (stack : Stack.t)
      (ref_core : Ref.Core.t A) :
      t (Output.t R A) :=
    match ref_core with
    | Ref.Core.Immediate value =>
      match value with
      | Some value => Pure (Output.Success value)
      | None => Pure (Output.Exception Output.Exception.BreakMatch)
      end
    | Ref.Core.Mutable _ _ _ _ _ =>
      GetCanAccess stack ref_core (fun H_can_access =>
      match Stack.CanAccess.read H_can_access with
      | Some value => Pure (Output.Success value)
      | None => Pure (Output.Exception Output.Exception.BreakMatch)
      end)
    end.

  Parameter TodoLoop : forall {A : Set}, t A.

  Fixpoint eval {R Output : Set}
      (e : LinkM.t R Output)
      (stack : Stack.t)
      {struct e} :
    t (Output.t R Output * Stack.t).
  Proof.
    destruct e.
    { (* Pure *)
      exact (Pure (value, stack)).
    }
    { (* CallPrimitive *)
      destruct primitive.
      { (* StateAlloc *)
        (* We always allocate an immediate value *)
        exact (eval _ _ (k (Ref.Core.Immediate (Some value))) stack).
      }
      { (* StateRead *)
        exact (
          let_ (read stack ref_core) (fun value =>
          match value with
          | Output.Success value =>
            eval _ _ (k value) stack
          | Output.Exception exception =>
            Pure (Output.Exception exception, stack)
          end)
        ).
      }
      { (* StateWrite *)
        refine (
          GetCanAccess stack ref_core (fun H_access =>
          _)
        ).
        destruct (Stack.CanAccess.write H_access value) as [stack'|].
        { exact (eval _ _ (k tt) stack'). }
        { exact (Pure (Output.Exception Output.Exception.BreakMatch, stack)). }
      }
      { (* GetSubPointer *)
        exact (eval _ _ (k (SubPointer.Runner.apply ref_core runner)) stack).
      }
    }
    { (* Let *)
      exact (
        let_ (eval _ _ e stack) (fun '(output, stack) =>
        eval _ _ (k output) stack)
      ).
    }
    { (* LetAlloc *)
      exact (
        let_ (eval _ _ e stack) (fun '(output, stack) =>
        match output with
        | Output.Success value =>
          let ref_core :=
            Ref.Core.Mutable
              (Stack.length stack)
              []
              φ
              Some
              (fun _ => Some) in
          let ref := {| Ref.core := ref_core |} in
          let stack := Stack.alloc stack value in
          let_ (eval _ _ (k (Output.Success ref)) stack) (fun '(output, stack) =>
          let stack := Stack.dealloc stack in
          Pure (output, stack))
        | Output.Exception exception => eval _ _ (k (Output.Exception exception)) stack
        end)
      ).
    }
    { (* Call *)
      exact (Call stack run_f0 (fun '(output, stack) =>
        eval _ _ (k output) stack
      )).
    }
    { (* Loop *)
      exact TodoLoop.
    }
    { (* IfThenElse *)
      exact (
        if cond then
          eval _ _ e1 stack
        else
          eval _ _ e2 stack
      ).
    }
    { (* MatchOutput *)
      exact (
        match output with
        | Output.Success success => eval _ _ (k_success success) stack
        | Output.Exception exception =>
          match exception with
          | Output.Exception.Return return_ => eval _ _ (k_return return_) stack
          | Output.Exception.Break => eval _ _ (k_break tt) stack
          | Output.Exception.Continue => eval _ _ (k_continue tt) stack
          | Output.Exception.BreakMatch => eval _ _ (k_break_match tt) stack
          end
        end
      ).
    }
    { (* Impossible *)
      exact (Impossible payload).
    }
  Defined.

  Definition eval_f
      {f : PolymorphicFunction.t}
      {ε : list Value.t}
      {τ : list Ty.t}
      {α : list Value.t}
      {Output : Set} `{Link Output}
      (run : Run.Trait f ε τ α Output) :
      Stack.t ->
      t (Output.t Output Output * Stack.t) :=
    eval (links.M.evaluate run.(Run.run_f)).
  Arguments eval_f _ _ _ _ _ _ _ _ /.
End SimulateM.
Export (notations) SimulateM.

Module Run.
  Reserved Notation "{{ e 🌲 value }}".

  Inductive t {A : Set} (value : A) : SimulateM.t A -> Prop :=
  | Pure :
    {{ SimulateM.Pure value 🌲 value }}
  | GetCanAccess {B : Set} `{Link B}
      (stack : Stack.t)
      (ref_core : Ref.Core.t B)
      (k : Stack.CanAccess.t stack ref_core -> SimulateM.t A)
      (H_access : Stack.CanAccess.t stack ref_core)
    (H_k : {{ k H_access 🌲 value }}) :
    {{ SimulateM.GetCanAccess stack ref_core k 🌲 value }}
  | Call {B : Set} `{Link B}
      {f : list Value.t -> M} {args : list Value.t}
      (stack_in : Stack.t)
      (run_f : {{ f args 🔽 B }})
      (output_inter : B)
      (stack_inter : Stack.t)
      (k : B * Stack.t -> SimulateM.t A)
    (H_f : {{ SimulateM.eval (links.M.evaluate run_f) stack_in 🌲 (Output.Success output_inter, stack_inter) }})
    (H_k : {{ k (output_inter, stack_inter) 🌲 value }}) :
    {{ SimulateM.Call stack_in run_f k 🌲 value }}

  where "{{ e 🌲 value }}" := (t value e).
End Run.
Export (notations) Run.

Ltac get_can_access :=
  unshelve eapply Run.GetCanAccess; [
    cbn;
    repeat constructor
  |];
  cbn.

Definition make_ref_core {A : Set} `{Link A} (index : nat) : Ref.Core.t A :=
  Ref.Core.Mutable (A := A) index [] φ Some (fun _ => Some).

Definition make_ref {A : Set} `{Link A} {kind : Pointer.Kind.t} (index : nat) : Ref.t kind A :=
  {| Ref.core := make_ref_core index |}.

(** To get a reference to a sub-field from a reference to a larger object. *)
Module RefStub.
  Record t {A Sub_A : Set} `{Link A} `{Link Sub_A} : Set := {
    path : Pointer.Path.t;
    (* We suppose the pointer is valid (no [option] type for the [projection] and [injection]
       functions) *)
    projection : A -> Sub_A;
    injection : A -> Sub_A -> A;
  }.
  Arguments t _ _ {_ _}.

  Definition apply_core {A Sub_A : Set} `{Link A} `{Link Sub_A}
      (ref_core : Ref.Core.t A)
      (stub : t A Sub_A) :
      Ref.Core.t Sub_A.
  Proof.
    destruct ref_core as [| ? ? address path big_to_value projection injection].
    { (* Immediate *)
      exact (
        Ref.Core.Immediate (
          match value with
          | Some a => Some (stub.(projection) a)
          | None => None
          end
        )
      ).
    }
    { (* Mutable *)
      exact (
        Ref.Core.Mutable
          address
          (path ++ stub.(RefStub.path))
          big_to_value
          (fun big_a =>
            match projection big_a with
            | Some a => Some (stub.(RefStub.projection) a)
            | None => None
            end
          )
          (fun big_a new_sub_a =>
            match projection big_a with
            | Some a =>
              let new_a := stub.(RefStub.injection) a new_sub_a in
              injection big_a new_a
            | None => None
            end
          )
      ).
    }
  Defined.

  Definition apply {A Sub_A : Set} `{Link A} `{Link Sub_A}
      {kind_source kind_target : Pointer.Kind.t}
      (ref : Ref.t kind_source A)
      (stub : t A Sub_A) :
      Ref.t kind_target Sub_A :=
    {| Ref.core := apply_core ref.(Ref.core) stub |}.
End RefStub.

(* This makes reasoning about arrays simpler, as now [cbn] works through [Z.to_nat]. *)
Arguments Pos.to_nat _ /.
