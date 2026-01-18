Require Import RocqOfRust.RocqOfRust.
Require Import links.M.
Require Import simulate.M.
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
    apply Run.Pure.
  Qed.
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
    cbn.
    eapply Run.Call. {
      apply Impl_MemoryGas.new_eq.
    }
    cbn.
    apply Run.Pure.
  Qed.

  (*
      pub const fn limit(&self) -> u64 {
          self.limit
      }
  *)
  Definition limit (self : Self) : u64 :=
    self.(Gas.limit).

  Lemma limit_eq (self : Self) :
    let ref_self := {|
      Ref.core := Ref.Core.Mutable (A := Self) 0%nat [] φ Some (fun _ => Some)
    |} in
    {{
      SimulateM.eval_f (Impl_Gas.run_limit ref_self) [self]%stack 🌲
      (Output.Success (limit self), [self]%stack)
    }}.
  Proof.
    with_strategy transparent [Impl_Gas.run_limit] cbn.
    progress repeat get_can_access.
    apply Run.Pure.
  Qed.

  (*
      pub fn erase_cost(&mut self, returned: u64) {
          self.remaining += returned;
      }
  *)
  Definition erase_cost (self : Self) (returned : u64) : Self :=
    {|
      Gas.limit := self.(Gas.limit);
      Gas.remaining :=
        {|
          Integer.value :=
            (self.(Gas.remaining).(Integer.value) + returned.(Integer.value)) mod 18446744073709551616
        |};
      Gas.refunded := self.(Gas.refunded);
      Gas.memory := self.(Gas.memory);
    |}.

  Lemma erase_cost_eq (self : Self) (returned : u64) :
    let ref_self := {|
      Ref.core := Ref.Core.Mutable (A := Self) 0%nat [] φ Some (fun _ => Some)
    |} in
    {{
      SimulateM.eval_f (Impl_Gas.run_erase_cost ref_self returned) [self]%stack 🌲
      (Output.Success tt, [erase_cost self returned]%stack)
    }}.
  Proof.
    with_strategy transparent [Impl_Gas.run_erase_cost] cbn.
    progress repeat get_can_access.
    eapply Run.Call. {
      apply Run.Pure.
    }
    cbn.
    repeat get_can_access.
    apply Run.Pure.
  Qed.

  (*
      pub fn record_cost(&mut self, cost: u64) -> bool {
        let (remaining, overflow) = self.remaining.overflowing_sub(cost);
        let success = !overflow;
        if success {
            self.remaining = remaining;
        }
        success
    }
  *)
  Definition record_cost (self : Self) (cost : u64) : option Self :=
    let (remaining, overflow) := Impl_u64.overflowing_sub self.(Gas.remaining) cost in
    let success := negb overflow in
    if success then
      Some (self <| Gas.remaining := remaining |>)
    else
      None.

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
    Opaque Impl_u64.overflowing_sub.
    apply Run.remove_extra_stack1.
    with_strategy transparent [Impl_Gas.run_record_cost] (
      unfold record_cost;
      cbn
    ).
    progress repeat get_can_access.
    eapply Run.Call. {
      apply Impl_u64.overflowing_sub_eq.
    }
    destruct Impl_u64.overflowing_sub as [remaining overflow].
    eapply Run.Call. {
      apply Run.Pure.
    }
    repeat progress get_can_access.
    eapply Run.Call. {
      apply Run.Pure.
    }
    destruct (negb overflow); cbn; progress repeat get_can_access.
    { apply Run.Pure. }
    { apply Run.Pure. }
    Transparent Impl_u64.overflowing_sub.
  Qed.
End Impl_Gas.
