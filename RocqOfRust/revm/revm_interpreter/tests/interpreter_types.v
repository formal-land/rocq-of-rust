Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.ops.links.range.
Require Import revm.revm_bytecode.eof.links.types_section.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import ruint.links.lib.

Parameter WIRE : Set.

Instance Link_WIRE : Link WIRE.
Admitted.

Module Stack.
  (** Note: we represent the list in reverse order to simplify access to the top in patterns *)
  Record t : Set := {
    value : list aliases.U256.t;
  }.

  Instance IsLink : Link t.
  Admitted.
End Stack.
Export (hints) Stack.

Module Control.
  Record t : Set := {
    gas : Gas.t;
    instruction_result : option InstructionResult.t;
  }.

  Instance IsLink : Link t.
  Admitted.
End Control.
Export (hints) Control.

Definition WIRE_types : InterpreterTypes.Types.t := {|
  InterpreterTypes.Types.Stack := Stack.t;
  InterpreterTypes.Types.Memory := unit;
  InterpreterTypes.Types.Memory_Synthetic := unit;
  InterpreterTypes.Types.Memory_Synthetic1 := unit;
  InterpreterTypes.Types.Bytecode := unit;
  InterpreterTypes.Types.ReturnData := unit;
  InterpreterTypes.Types.Input := unit;
  InterpreterTypes.Types.SubRoutineStack := unit;
  InterpreterTypes.Types.Control := Control.t;
  InterpreterTypes.Types.RuntimeFlag := unit;
  InterpreterTypes.Types.Extend := unit;
|}.

Instance AreLinks_WIRE_types : InterpreterTypes.Types.AreLinks WIRE_types := {}.

Module Immediates.
  Instance I : Immediates.C WIRE_types.(InterpreterTypes.Types.Bytecode).
  Admitted.
End Immediates.
Export (hints) Immediates.

Module LegacyBytecode.
  Instance I : LegacyBytecode.C WIRE_types.(InterpreterTypes.Types.Bytecode).
  Admitted.
End LegacyBytecode.
Export (hints) LegacyBytecode.

Module Jumps.
  Instance I : Jumps.C WIRE_types.(InterpreterTypes.Types.Bytecode).
  Admitted.
End Jumps.
Export (hints) Jumps.

Module EofData.
  Instance I : EofData.C WIRE_types.(InterpreterTypes.Types.Bytecode).
  Admitted.
End EofData.
Export (hints) EofData.

Module EofContainer.
  Instance I : EofContainer.C WIRE_types.(InterpreterTypes.Types.Bytecode).
  Admitted.
End EofContainer.
Export (hints) EofContainer.

Module EofCodeInfo.
  Instance I : EofCodeInfo.C WIRE_types.(InterpreterTypes.Types.Bytecode).
  Admitted.
End EofCodeInfo.
Export (hints) EofCodeInfo.

Module InputTraits.
  Instance I : InputTraits.C WIRE_types.(InterpreterTypes.Types.Input).
  Admitted.
End InputTraits.
Export (hints) InputTraits.

Module StackTrait.
  Definition Self : Set :=
    Stack.t.

  Definition len (self : Self) : usize :=
    Z.of_nat (List.length self.(Stack.value)).

  Definition is_empty (self : Self) : bool :=
    match self.(Stack.value) with
    | [] => true
    | _ => false
    end.

  (* TODO: check spec *)
  Definition push (self : Self) (value : aliases.U256.t) : bool * Self :=
    let MAX_LEN := Z.of_nat 1024 in
    if i[len self] <=? MAX_LEN then
      (true, self <| Stack.value := value :: self.(Stack.value) |>)
    else
      (false, self).

  Definition push_b256 (self : Self) (value : aliases.B256.t) : bool * Self.
  Admitted.

  (* TODO: check spec: do we let the stack as empty if the stack is too short? *)
  Fixpoint popn_nat (N : nat) (self : Self) : option (ArrayPairs.t aliases.U256.t N) * Self :=
    match N with
    | O => (Some ArrayEmpty.Make, self)
    | S N =>
      match self.(Stack.value) with
      | [] => (None, self)
      | value :: rest =>
        let '(result, self') := popn_nat N (self <| Stack.value := rest |>) in
        match result with
        | Some values => (Some {| ArrayPair.x := value; ArrayPair.xs := values |}, self')
        | None => (None, self')
        end
      end
    end.

  Definition popn (N : usize) (self : Self) : option (array.t aliases.U256.t N) * Self :=
    let '(result, self') := popn_nat (Z.to_nat i[N]) self in
    match result with
    | Some values => (Some {| array.value := values |}, self')
    | None => (None, self')
    end.

  Definition top (self : Self) : option (RefStub.t Self aliases.U256.t) :=
    match self.(Stack.value) with
    | [] => None
    | default_value :: _ =>
      Some {|
        RefStub.path := [];
        RefStub.projection x :=
          match x.(Stack.value) with
          | [] => default_value (* impossible *)
          | value :: _ => value
          end;
        RefStub.injection x value :=
          match x.(Stack.value) with
          | [] => {| Stack.value := [] |} (* impossible *)
          | _ :: rest => {| Stack.value := value :: rest |}
          end;
      |}
    end.

  Definition popn_top (N : usize) (self : Self) :
      option (array.t aliases.U256.t N * RefStub.t Self aliases.U256.t) * Self :=
    let '(result, self') := popn N self in
    match result with
    | Some values =>
      let top_stub := top self' in
      match top_stub with
      | Some top_stub => (Some (values, top_stub), self')
      | None => (None, self')
      end
    | None => (None, self')
    end.

  Definition pop (self : Self) : option aliases.U256.t * Self.
  Admitted.

  Definition pop_address (self : Self) : option Address.t * Self.
  Admitted.

  Definition exchange (self : Self) (n m : usize) : bool * Self.
  Admitted.

  Definition dup (self : Self) (n : usize) : bool * Self.
  Admitted.

  Instance I : StackTrait.C WIRE_types.(InterpreterTypes.Types.Stack) := {
    StackTrait.len := len;
    StackTrait.is_empty := is_empty;
    StackTrait.push := push;
    StackTrait.push_b256 := push_b256;
    StackTrait.popn := popn;
    StackTrait.popn_top := popn_top;
    StackTrait.top := top;
    StackTrait.pop := pop;
    StackTrait.pop_address := pop_address;
    StackTrait.exchange := exchange;
    StackTrait.dup := dup;
  }.
End StackTrait.
Export (hints) StackTrait.

Module LoopControl.
  Definition Self : Set :=
    Control.t.

  Definition set_instruction_result (self : Self) (result : InstructionResult.t) : Self :=
    self <| Control.instruction_result := Some result |>.

  Definition set_next_action
      (self : Self)
      (action : InterpreterAction.t)
      (result : InstructionResult.t) :
      Self.
  Admitted.

  Definition gas : RefStub.t Self Gas.t := {|
    RefStub.path := [];
    RefStub.projection := fun x => x.(Control.gas);
    RefStub.injection := fun x y => x <| Control.gas := y |>;
  |}.

  Definition instruction_result (self : Self) : InstructionResult.t.
  Admitted.

  Definition take_next_action (self : Self) : InterpreterAction.t * Self.
  Admitted.

  Instance I : LoopControl.C WIRE_types.(InterpreterTypes.Types.Control) := {|
    simulate.interpreter_types.LoopControl.set_instruction_result := set_instruction_result;
    simulate.interpreter_types.LoopControl.set_next_action := set_next_action;
    simulate.interpreter_types.LoopControl.gas := gas;
    simulate.interpreter_types.LoopControl.instruction_result := instruction_result;
    simulate.interpreter_types.LoopControl.take_next_action := take_next_action;
  |}.
End LoopControl.
Export (hints) LoopControl.

Module RuntimeFlag.
  Instance I : RuntimeFlag.C WIRE_types.(InterpreterTypes.Types.RuntimeFlag).
  Admitted.
End RuntimeFlag.
Export (hints) RuntimeFlag.

Module MemoryTrait.
  Instance I : MemoryTrait.C WIRE_types.(InterpreterTypes.Types.Memory)
    WIRE_types.(InterpreterTypes.Types.Memory_Synthetic)
    WIRE_types.(InterpreterTypes.Types.Memory_Synthetic1).
  Admitted.
End MemoryTrait.
Export (hints) MemoryTrait.

Module SubRoutineStack.
  Instance I : SubRoutineStack.C WIRE_types.(InterpreterTypes.Types.SubRoutineStack).
  Admitted.
End SubRoutineStack.
Export (hints) SubRoutineStack.

Module ReturnData.
  Instance I : ReturnData.C WIRE_types.(InterpreterTypes.Types.ReturnData).
  Admitted.
End ReturnData.
Export (hints) ReturnData.

Module InterpreterTypes.
  Instance I : InterpreterTypes.C WIRE_types := {}.
End InterpreterTypes.
Export (hints) InterpreterTypes.
