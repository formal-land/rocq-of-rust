Require Import simulate.RocqOfRust.
Require Import core.num.simulate.mod.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.

Module Impl_MemoryGas.
  Definition Self : Set :=
    MemoryGas.t.

  Definition new : Self :=
    {|
      MemoryGas.words_num := {| Integer.value := 0 |};
      MemoryGas.expansion_cost := {| Integer.value := 0 |};
    |}.

  Lemma new_eq (stack : Stack.t) :
    {{
      SimulateM.eval_f Impl_MemoryGas.run_new stack 🌲
      (Output.Success new, stack)
  }}.
  Proof.
    Transparent revm.revm_interpreter.links.gas.Impl_Gas.run_memory.
    unfold revm.revm_interpreter.links.gas.Impl_Gas.run_memory.
    cbn.
    p.
    Opaque revm.revm_interpreter.links.gas.Impl_Gas.run_memory.
  Qed.

  Definition record_new_len (self : Self) (new_num : usize) : option u64 * Self :=
    (Some (0 : u64), self).

  Lemma record_new_len_eq
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (interpreter : Interpreter.t WIRE WIRE_types)
      (gas_stub : RefStub.t WIRE_types.(InterpreterTypes.Types.Control) Gas.t)
      (new_num : usize)
      (stack : Stack.t) :
    let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
    let ref_control : '&mut _ := {| Ref.core :=
        SubPointer.Runner.apply
          ref_interpreter.(Ref.core)
          Interpreter.SubPointer.get_control
    |} in
    let ref_gas : '&mut _ := RefStub.apply ref_control gas_stub in
    let ref_self := {| Ref.core :=
        SubPointer.Runner.apply
          ref_gas.(Ref.core)
          Gas.SubPointer.get_memory
    |} in
    let gas := gas_stub.(RefStub.projection) interpreter.(Interpreter.control) in
    let memory_gas := gas.(Gas.memory) in
    let result := record_new_len memory_gas new_num in
    {{
      SimulateM.eval_f (Impl_MemoryGas.run_record_new_len ref_self new_num) (interpreter :: stack)%stack 🌲
      (
        Output.Success (fst result),
        (
          (interpreter <| Interpreter.control :=
            gas_stub.(RefStub.injection)
              interpreter.(Interpreter.control)
              (gas <| Gas.memory := snd result |>)
          |>) :: stack
        )%stack
      )
    }}.
  Proof.
  Admitted.
End Impl_MemoryGas.

Module Impl_Gas.
  Definition Self : Set :=
    Gas.t.

  Definition new (limit : u64) : Self :=
    {|
      Gas.limit := limit;
      Gas.remaining := limit;
      Gas.refunded := {| Integer.value := 0 |};
      Gas.memory := Impl_MemoryGas.new;
    |}.

  Lemma new_eq (limit : u64) :
    {{
      SimulateM.eval_f (Impl_Gas.run_new limit) []%stack 🌲
      (Output.Success (new limit), []%stack)
    }}.
  Proof.
    repeat s.
  Qed.

  Definition new_spent (limit : u64) : Self :=
    {|
      Gas.limit := limit;
      Gas.remaining := {| Integer.value := 0 |};
      Gas.refunded := {| Integer.value := 0 |};
      Gas.memory := Impl_MemoryGas.new;
    |}.

  Lemma new_spent_eq (limit : u64) :
    {{
      SimulateM.eval_f (Impl_Gas.run_new_spent limit) []%stack 🌲
      (Output.Success (new_spent limit), []%stack)
    }}.
  Proof.
    repeat s.
  Qed.

  Definition limit (self : Self) : u64 :=
    self.(Gas.limit).

  Lemma limit_eq (ref_self : '& Self) (self : Self) (stack : Stack.t) :
      CanRead.t stack self ref_self ->
    {{
      SimulateM.eval_f (Impl_Gas.run_limit ref_self) stack 🌲
      (Output.Success (limit self), stack)
    }}.
  Proof.
  Admitted.

  Definition memory : RefStub.t Self MemoryGas.t := {|
    RefStub.path := [Pointer.Index.StructRecord "revm_interpreter::gas::Gas" "memory"];
    RefStub.projection := Gas.memory;
    RefStub.injection := fun self memory => self <| Gas.memory := memory |>;
  |}.

  Lemma memory_eq
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (interpreter : Interpreter.t WIRE WIRE_types)
      (gas_stub : RefStub.t WIRE_types.(InterpreterTypes.Types.Control) Gas.t)
      (stack : Stack.t) :
    let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
    let ref_control : '&mut _ := {| Ref.core :=
        SubPointer.Runner.apply
          ref_interpreter.(Ref.core)
          Interpreter.SubPointer.get_control
    |} in
    let ref_self := RefStub.apply ref_control gas_stub in
    {{
      SimulateM.eval_f (Impl_Gas.run_memory ref_self) (interpreter :: stack)%stack 🌲
      (Output.Success (RefStub.apply ref_self memory), interpreter :: stack)%stack
    }}.
  Admitted.

  Lemma memory_interpreter_eq
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (interpreter : Interpreter.t WIRE WIRE_types)
      (stack : Stack.t) :
    let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
    let ref_self : '& _ := {| Ref.core :=
        SubPointer.Runner.apply
          ref_interpreter.(Ref.core)
          Interpreter.SubPointer.get_gas
    |} in
    {{
      SimulateM.eval_f (Impl_Gas.run_memory ref_self) (interpreter :: stack)%stack 🌲
      (
        Output.Success (RefStub.apply ref_self memory),
        (interpreter :: stack)%stack
      )
    }}.
  Proof.
    apply Run.remove_extra_stack1.
    with_strategy transparent [Impl_Gas.run_memory] cbn.
    s.
  Qed.

  Lemma memory_mut_interpreter_eq
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (interpreter : Interpreter.t WIRE WIRE_types)
      (stack : Stack.t) :
    let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
    let ref_self : '&mut _ := {| Ref.core :=
        SubPointer.Runner.apply
          ref_interpreter.(Ref.core)
          Interpreter.SubPointer.get_gas
    |} in
    {{
      SimulateM.eval_f (Impl_Gas.run_memory_mut ref_self) (interpreter :: stack)%stack 🌲
      (
        Output.Success (RefStub.apply ref_self memory),
        (interpreter :: stack)%stack
      )
    }}.
  Proof.
    apply Run.remove_extra_stack1.
    with_strategy transparent [Impl_Gas.run_memory_mut] cbn.
    s.
  Qed.

  Definition refunded (self : Self) : i64 :=
    self.(Gas.refunded).

  Lemma refunded_eq
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (interpreter : Interpreter.t WIRE WIRE_types)
      (gas_stub : RefStub.t WIRE_types.(InterpreterTypes.Types.Control) Gas.t)
      (stack : Stack.t) :
    let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
    let ref_control : '&mut _ := {| Ref.core :=
        SubPointer.Runner.apply
          ref_interpreter.(Ref.core)
          Interpreter.SubPointer.get_control
    |} in
    let ref_self := RefStub.apply ref_control gas_stub in
    let self := gas_stub.(RefStub.projection) interpreter.(Interpreter.control) in
    {{
      SimulateM.eval_f (Impl_Gas.run_refunded ref_self) (interpreter :: stack)%stack 🌲
      (Output.Success (refunded self), interpreter :: stack)%stack
    }}.
  Proof.
    with_strategy transparent [Impl_Gas.run_refunded] cbn.
    p.
  Qed.

  Definition spent (self : Self) : u64 :=
    self.(Gas.limit) -i self.(Gas.remaining).

  Lemma spent_eq
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (interpreter : Interpreter.t WIRE WIRE_types)
      (gas_stub : RefStub.t WIRE_types.(InterpreterTypes.Types.Control) Gas.t)
      (stack : Stack.t) :
    let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
    let ref_control : '&mut _ := {| Ref.core :=
        SubPointer.Runner.apply
          ref_interpreter.(Ref.core)
          Interpreter.SubPointer.get_control
    |} in
    let ref_self := RefStub.apply ref_control gas_stub in
    let self := gas_stub.(RefStub.projection) interpreter.(Interpreter.control) in
    {{
      SimulateM.eval_f (Impl_Gas.run_spent ref_self) (interpreter :: stack)%stack 🌲
      (Output.Success (spent self), interpreter :: stack)%stack
    }}.
  Proof.
    with_strategy transparent [Impl_Gas.run_spent] cbn.
    s.
  Qed.

  Definition remaining (self : Self) : u64 :=
    self.(Gas.remaining).

  Lemma remaining_eq
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (interpreter : Interpreter.t WIRE WIRE_types)
      (gas_stub : RefStub.t WIRE_types.(InterpreterTypes.Types.Control) Gas.t)
      (stack : Stack.t) :
    let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
    let ref_control : '&mut _ := {| Ref.core :=
        SubPointer.Runner.apply
          ref_interpreter.(Ref.core)
          Interpreter.SubPointer.get_control
    |} in
    let ref_self := RefStub.apply ref_control gas_stub in
    let self := gas_stub.(RefStub.projection) interpreter.(Interpreter.control) in
    {{
      SimulateM.eval_f (Impl_Gas.run_remaining ref_self) (interpreter :: stack)%stack 🌲
      (Output.Success (remaining self), interpreter :: stack)%stack
    }}.
  Proof.
    with_strategy transparent [Impl_Gas.run_remaining] cbn.
    p.
  Qed.

  Lemma remaining_interpreter_eq
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (interpreter : Interpreter.t WIRE WIRE_types)
      (stack : Stack.t) :
    let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
    let ref_self : '& _ := {|
      Ref.core :=
        SubPointer.Runner.apply
          ref_interpreter.(Ref.core)
          Interpreter.SubPointer.get_gas
    |} in
    {{
      SimulateM.eval_f (Impl_Gas.run_remaining ref_self) (interpreter :: stack)%stack 🌲
      (Output.Success (remaining interpreter.(Interpreter.gas)), interpreter :: stack)%stack
    }}.
  Proof.
    with_strategy transparent [Impl_Gas.run_remaining] cbn.
    p.
  Qed.

  Definition remaining_63_of_64_parts (self : Self) : u64 :=
    self.(Gas.remaining) -i self.(Gas.remaining) /i 64.

  Lemma remaining_63_of_64_parts_eq
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (interpreter : Interpreter.t WIRE WIRE_types)
      (gas_stub : RefStub.t WIRE_types.(InterpreterTypes.Types.Control) Gas.t)
      (stack : Stack.t) :
    let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
    let ref_control : '&mut _ := {| Ref.core :=
        SubPointer.Runner.apply
          ref_interpreter.(Ref.core)
          Interpreter.SubPointer.get_control
    |} in
    let ref_self := RefStub.apply ref_control gas_stub in
    let self := gas_stub.(RefStub.projection) interpreter.(Interpreter.control) in
    {{
      SimulateM.eval_f (Impl_Gas.run_remaining_63_of_64_parts ref_self) (interpreter :: stack)%stack 🌲
      (Output.Success (remaining_63_of_64_parts self), interpreter :: stack)%stack
    }}.
  Proof.
    with_strategy transparent [Impl_Gas.run_remaining_63_of_64_parts] cbn.
    s.
  Qed.

  Definition erase_cost (self : Self) (returned : u64) : Self :=
    self <| Gas.remaining := self.(Gas.remaining) +i returned |>.

  Lemma erase_cost_eq
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (interpreter : Interpreter.t WIRE WIRE_types)
      (gas_stub : RefStub.t WIRE_types.(InterpreterTypes.Types.Control) Gas.t)
      (returned : u64)
      (stack : Stack.t) :
    let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
    let ref_control : '&mut _ := {| Ref.core :=
        SubPointer.Runner.apply
          ref_interpreter.(Ref.core)
          Interpreter.SubPointer.get_control
    |} in
    let ref_self := RefStub.apply ref_control gas_stub in
    let self := gas_stub.(RefStub.projection) interpreter.(Interpreter.control) in
    let result := erase_cost self returned in
    {{
      SimulateM.eval_f (Impl_Gas.run_erase_cost ref_self returned) (interpreter :: stack)%stack 🌲
      (Output.Success tt, (
        (interpreter <| Interpreter.control :=
          gas_stub.(RefStub.injection) interpreter.(Interpreter.control) (erase_cost self returned)
        |>) :: stack
      )%stack
      )
    }}.
  Proof.
    apply Run.remove_extra_stack1.
    with_strategy transparent [Impl_Gas.run_erase_cost] cbn.
    s.
  Qed.

  Definition spend_all (self : Self) : Self :=
    self <| Gas.remaining := 0 |>.

  Lemma spend_all_eq
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (interpreter : Interpreter.t WIRE WIRE_types)
      (gas_stub : RefStub.t WIRE_types.(InterpreterTypes.Types.Control) Gas.t)
      (stack : Stack.t) :
    let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
    let ref_control : '&mut _ := {| Ref.core :=
        SubPointer.Runner.apply
          ref_interpreter.(Ref.core)
          Interpreter.SubPointer.get_control
    |} in
    let ref_self := RefStub.apply ref_control gas_stub in
    let self := gas_stub.(RefStub.projection) interpreter.(Interpreter.control) in
    let result := spend_all self in
    {{
      SimulateM.eval_f (Impl_Gas.run_spend_all ref_self) (interpreter :: stack)%stack 🌲
      (
        Output.Success tt,
        (
          (interpreter <| Interpreter.control :=
            gas_stub.(RefStub.injection) interpreter.(Interpreter.control) result
          |>) :: stack
        )%stack
      )
    }}.
  Proof.
    apply Run.remove_extra_stack1.
    with_strategy transparent [Impl_Gas.run_spend_all] cbn.
    s.
  Qed.

  Lemma spend_all_interpreter_eq
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (interpreter : Interpreter.t WIRE WIRE_types)
      (stack : Stack.t) :
    let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
    let ref_self : '&mut _ := {| Ref.core :=
        SubPointer.Runner.apply
          ref_interpreter.(Ref.core)
          Interpreter.SubPointer.get_gas
    |} in
    let result := spend_all interpreter.(Interpreter.gas) in
    {{
      SimulateM.eval_f (Impl_Gas.run_spend_all ref_self) (interpreter :: stack)%stack 🌲
      (
        Output.Success tt,
        (
          (interpreter <| Interpreter.gas := result |>) :: stack
        )%stack
      )
    }}.
  Proof.
    apply Run.remove_extra_stack1.
    with_strategy transparent [Impl_Gas.run_spend_all] cbn.
    s.
  Qed.

  Definition record_refund (self : Self) (refund : i64) : Self :=
    self <| Gas.refunded := self.(Gas.refunded) +i refund |>.

  Lemma record_refund_eq
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (interpreter : Interpreter.t WIRE WIRE_types)
      (gas_stub : RefStub.t WIRE_types.(InterpreterTypes.Types.Control) Gas.t)
      (refund : i64)
      (stack : Stack.t) :
    let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
    let ref_control : '&mut _ := {| Ref.core :=
        SubPointer.Runner.apply
          ref_interpreter.(Ref.core)
          Interpreter.SubPointer.get_control
    |} in
    let ref_self := RefStub.apply ref_control gas_stub in
    let self := gas_stub.(RefStub.projection) interpreter.(Interpreter.control) in
    let result := record_refund self refund in
    {{
      SimulateM.eval_f (Impl_Gas.run_record_refund ref_self refund) (interpreter :: stack)%stack 🌲
      (
        Output.Success tt,
        (
          (interpreter <| Interpreter.control :=
            gas_stub.(RefStub.injection) interpreter.(Interpreter.control) result
          |>) :: stack
        )%stack
      )
    }}.
  Proof.
    apply Run.remove_extra_stack1.
    with_strategy transparent [Impl_Gas.run_record_refund] cbn.
    s.
  Qed.

  Lemma record_refund_interpreter_eq
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (interpreter : Interpreter.t WIRE WIRE_types)
      (refund : i64)
      (stack : Stack.t) :
    let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
    let ref_self : '&mut _ := {| Ref.core :=
        SubPointer.Runner.apply
          ref_interpreter.(Ref.core)
          Interpreter.SubPointer.get_gas
    |} in
    let result := record_refund interpreter.(Interpreter.gas) refund in
    {{
      SimulateM.eval_f (Impl_Gas.run_record_refund ref_self refund) (interpreter :: stack)%stack 🌲
      (
        Output.Success tt,
        (
          (interpreter <| Interpreter.gas := result |>) :: stack
        )%stack
      )
    }}.
  Proof.
    apply Run.remove_extra_stack1.
    with_strategy transparent [Impl_Gas.run_record_refund] cbn.
    s.
  Qed.

  Definition set_final_refund (self : Self) (is_london : bool) : Self :=
    let max_refund_quotient := if is_london then 5 else 2 in
    self <| Gas.refunded := Z.min i[refunded self] i[spent self /i max_refund_quotient] |>.

  Lemma set_final_refund_eq
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (interpreter : Interpreter.t WIRE WIRE_types)
      (gas_stub : RefStub.t WIRE_types.(InterpreterTypes.Types.Control) Gas.t)
      (is_london : bool)
      (stack : Stack.t) :
    let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
    let ref_control : '&mut _ := {| Ref.core :=
        SubPointer.Runner.apply
          ref_interpreter.(Ref.core)
          Interpreter.SubPointer.get_control
    |} in
    let ref_self := RefStub.apply ref_control gas_stub in
    let self := gas_stub.(RefStub.projection) interpreter.(Interpreter.control) in
    let result := set_final_refund self is_london in
    {{
      SimulateM.eval_f (Impl_Gas.run_set_final_refund ref_self is_london) (interpreter :: stack)%stack 🌲
      (
        Output.Success tt,
        (
          (interpreter <| Interpreter.control :=
            gas_stub.(RefStub.injection) interpreter.(Interpreter.control) result
          |>) :: stack
        )%stack
      )
    }}.
  Proof.
    apply Run.remove_extra_stack1.
    with_strategy transparent [Impl_Gas.run_set_final_refund] cbn.
    unfold set_final_refund.
    destruct is_london;
      (s; [apply refunded_eq |]);
      (s; [apply spent_eq |]);
      s.
  Admitted.

  Definition set_refund (self : Self) (refund : i64) : Self :=
    self <| Gas.refunded := refund |>.

  Lemma set_refund_eq
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (interpreter : Interpreter.t WIRE WIRE_types)
      (gas_stub : RefStub.t WIRE_types.(InterpreterTypes.Types.Control) Gas.t)
      (refund : i64)
      (stack : Stack.t) :
    let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
    let ref_control : '&mut _ := {| Ref.core :=
        SubPointer.Runner.apply
          ref_interpreter.(Ref.core)
          Interpreter.SubPointer.get_control
    |} in
    let ref_self := RefStub.apply ref_control gas_stub in
    let gas := gas_stub.(RefStub.projection) interpreter.(Interpreter.control) in
    let result := set_refund gas refund in
    {{
      SimulateM.eval_f (Impl_Gas.run_set_refund ref_self refund) (interpreter :: stack)%stack 🌲
      (
        Output.Success tt,
        (
          (interpreter <| Interpreter.control :=
            gas_stub.(RefStub.injection) interpreter.(Interpreter.control) result
          |>) :: stack
        )%stack
      )
    }}.
  Proof.
    apply Run.remove_extra_stack1.
    with_strategy transparent [Impl_Gas.run_set_refund] cbn.
    s.
  Qed.

  Definition record_cost (self : Self) (cost : u64) : option Self :=
    match Impl_u64.checked_sub self.(Gas.remaining) cost with
    | Some remaining =>
      Some (self <| Gas.remaining := remaining |>)
    | None =>
      None
    end.

  Lemma record_cost_eq
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (interpreter : Interpreter.t WIRE WIRE_types)
      (gas_stub : RefStub.t WIRE_types.(InterpreterTypes.Types.Control) Gas.t)
      (cost : u64)
      (stack : Stack.t) :
    let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
    let ref_control : '&mut _ := {| Ref.core :=
        SubPointer.Runner.apply
          ref_interpreter.(Ref.core)
          Interpreter.SubPointer.get_control
    |} in
    let ref_self := RefStub.apply ref_control gas_stub in
    let gas := gas_stub.(RefStub.projection) interpreter.(Interpreter.control) in
    let result := record_cost gas cost in
    {{
      SimulateM.eval_f (Impl_Gas.run_record_cost ref_self cost) (interpreter :: stack)%stack 🌲
      (
        Output.Success (
          match result with
          | None => false
          | Some _ => true
          end
        ),
        (
          (interpreter <| Interpreter.control :=
            match result with
            | None => interpreter.(Interpreter.control)
            | Some gas => gas_stub.(RefStub.injection) interpreter.(Interpreter.control) gas
            end
          |>) :: stack
        )%stack
      )
    }}.
  Proof.
    apply Run.remove_extra_stack1.
    with_strategy transparent [Impl_Gas.run_record_cost] (
      unfold record_cost;
      cbn
    ).
    s.
    { apply Impl_u64.checked_sub_eq. }
    { destruct (Impl_u64.checked_sub
        (gas_stub.(RefStub.projection) interpreter.(Interpreter.control)).(Gas.remaining)
        cost); cbn.
      { s. }
      { repeat (lu || p). }
    }
  Qed.

  Lemma record_cost_interpreter_eq
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (interpreter : Interpreter.t WIRE WIRE_types)
      (cost : u64)
      (stack : Stack.t) :
    let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
    let ref_self : '&mut _ := {| Ref.core :=
        SubPointer.Runner.apply
          ref_interpreter.(Ref.core)
          Interpreter.SubPointer.get_gas
    |} in
    let result := record_cost interpreter.(Interpreter.gas) cost in
    {{
      SimulateM.eval_f (Impl_Gas.run_record_cost ref_self cost) (interpreter :: stack)%stack 🌲
      (
        Output.Success (
          match result with
          | None => false
          | Some _ => true
          end
        ),
        (
          match result with
          | None => interpreter
          | Some gas => interpreter <| Interpreter.gas := gas |>
          end :: stack
        )%stack
      )
    }}.
  Proof.
    apply Run.remove_extra_stack1.
    with_strategy transparent [Impl_Gas.run_record_cost] (
      unfold record_cost;
      cbn
    ).
    s.
    { apply Impl_u64.checked_sub_eq. }
    { destruct (Impl_u64.checked_sub interpreter.(Interpreter.gas).(Gas.remaining) cost); cbn.
      { s. }
      { repeat (lu || p). }
    }
  Qed.

  (* Help some proofs later *)
  Global Opaque record_cost.

End Impl_Gas.
