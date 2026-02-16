Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.ops.links.range.
Require Import core.ops.simulate.deref.
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

(** Memory represented as a list of bytes *)
Module Memory.
  Record t : Set := {
    value : list u8;
  }.

  Instance IsLink : Link t.
  Admitted.

  (** Take n elements from list, padding with zeros if too short *)
  Fixpoint take_pad (len : nat) (l : list u8) : list u8 :=
    match len with
    | O => []
    | S n =>
      match l with
      | [] => (0 : u8) :: take_pad n []
      | x :: rest => x :: take_pad n rest
      end
    end.

  (** Get a slice of memory, returning zeros for out-of-bounds *)
  Definition slice (self : t) (offset len : usize) : list u8 :=
    take_pad (Z.to_nat i[len]) (List.skipn (Z.to_nat i[offset]) self.(value)).

  (** Extend list to given length, padding with zeros *)
  Fixpoint extend_to (l : list u8) (len : nat) : list u8 :=
    match len with
    | O => l
    | S n =>
      match l with
      | [] => (0 : u8) :: extend_to (@nil u8) n
      | x :: rest => x :: extend_to rest n
      end
    end.

  (** Set bytes at offset: prefix ++ data ++ suffix *)
  Definition set_bytes_at (l : list u8) (offset : nat) (data : list u8) : list u8 :=
    let prefix := take_pad offset l in
    let suffix := List.skipn (offset + List.length data) l in
    prefix ++ data ++ suffix.

  Definition set (self : t) (offset : usize) (data : list u8) : t :=
    {| value := set_bytes_at self.(value) (Z.to_nat i[offset]) data |}.

  Definition set_data (self : t) (memory_offset data_offset len : usize) (data : list u8) : t :=
    let src := List.skipn (Z.to_nat i[data_offset]) data in
    let to_copy := List.firstn (Z.to_nat i[len]) src in
    set self memory_offset to_copy.

  Definition copy (self : t) (dst src len : usize) : t :=
    let data := slice self src len in
    set self dst data.

  Definition resize (self : t) (new_size : usize) : t :=
    {| value := extend_to self.(value) (Z.to_nat i[new_size]) |}.

  Definition size (self : t) : usize :=
    Z.of_nat (List.length self.(value)).
End Memory.
Export (hints) Memory.

(** Synthetic slice type for memory - just a list of bytes *)
Module MemorySlice.
  Definition t : Set := list u8.

  (** Deref implementation - identity function *)
  Instance Deref_I : Deref.C t (list u8) := {|
    Deref.deref := {|
      RefStub.path := [];
      RefStub.projection := fun x => x;
      RefStub.injection := fun _ y => y;
    |};
  |}.
End MemorySlice.
Export (hints) MemorySlice.

Module Control.
  Record t : Set := {
    gas : Gas.t;
    instruction_result : option InstructionResult.t;
    next_action : option InterpreterAction.t;
  }.

  Instance IsLink : Link t.
  Admitted.
End Control.
Export (hints) Control.

Definition WIRE_types : InterpreterTypes.Types.t := {|
  InterpreterTypes.Types.Stack := Stack.t;
  InterpreterTypes.Types.Memory := Memory.t;
  InterpreterTypes.Types.Memory_Synthetic := MemorySlice.t;
  InterpreterTypes.Types.Memory_Synthetic1 := MemorySlice.t;
  InterpreterTypes.Types.Bytecode := usize;
  InterpreterTypes.Types.ReturnData := unit;
  InterpreterTypes.Types.Input := unit;
  InterpreterTypes.Types.SubRoutineStack := unit;
  InterpreterTypes.Types.Control := Control.t;
  InterpreterTypes.Types.RuntimeFlag := SpecId.t;
  InterpreterTypes.Types.Extend := unit;
|}.

Instance AreLinks_WIRE_types : InterpreterTypes.Types.AreLinks WIRE_types := {}.

Module Immediates.
  Definition Self : Set := usize.

  Definition read_i16 (self : Self) : i16 := 0.
  Definition read_u16 (self : Self) : u16 := 0.
  Definition read_i8 (self : Self) : i8 := 0.
  Definition read_u8 (self : Self) : u8 := 0.
  Definition read_offset_i16 (self : Self) (offset : isize) : i16 := 0.
  Definition read_offset_u16 (self : Self) (offset : isize) : u16 := 0.
  Definition read_slice (len : usize) : RefStub.t Self (list u8) := {|
    RefStub.path := [];
    RefStub.projection := fun _ => List.repeat (0 : u8) (Z.to_nat i[len]);
    RefStub.injection := fun x _ => x;
  |}.

  Instance I : Immediates.C WIRE_types.(InterpreterTypes.Types.Bytecode) := {|
    simulate.interpreter_types.Immediates.read_i16 := read_i16;
    simulate.interpreter_types.Immediates.read_u16 := read_u16;
    simulate.interpreter_types.Immediates.read_i8 := read_i8;
    simulate.interpreter_types.Immediates.read_u8 := read_u8;
    simulate.interpreter_types.Immediates.read_offset_i16 := read_offset_i16;
    simulate.interpreter_types.Immediates.read_offset_u16 := read_offset_u16;
    simulate.interpreter_types.Immediates.read_slice := read_slice;
  |}.
End Immediates.
Export (hints) Immediates.

Module LegacyBytecode.
  Instance I : LegacyBytecode.C WIRE_types.(InterpreterTypes.Types.Bytecode).
  Admitted.
End LegacyBytecode.
Export (hints) LegacyBytecode.

Module Jumps.
  Definition Self : Set := usize.

  Definition relative_jump (self : Self) (offset : isize) : Self :=
    {| Integer.value := i[self] + i[offset] |}.
  Definition absolute_jump (_self : Self) (offset : usize) : Self := offset.
  Definition is_valid_legacy_jump (self : Self) (_offset : usize) : bool * Self := (true, self).
  Definition pc (self : Self) : usize := self.
  Definition opcode (self : Self) : u8 := 0.

  Instance I : Jumps.C WIRE_types.(InterpreterTypes.Types.Bytecode) := {|
    simulate.interpreter_types.Jumps.relative_jump := relative_jump;
    simulate.interpreter_types.Jumps.absolute_jump := absolute_jump;
    simulate.interpreter_types.Jumps.is_valid_legacy_jump := is_valid_legacy_jump;
    simulate.interpreter_types.Jumps.pc := pc;
    simulate.interpreter_types.Jumps.opcode := opcode;
  |}.
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
    if i[len self] <=? MAX_LEN - 1 then
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

  Definition pop (self : Self) : option aliases.U256.t * Self :=
    match self.(Stack.value) with
    | [] => (None, self)
    | value :: rest => (Some value, {| Stack.value := rest |})
    end.

  Definition pop_address (self : Self) : option Address.t * Self :=
    match self.(Stack.value) with
    | [] => (None, self)
    | value :: rest =>
      (Some {| Address.value := value.(Uint.value) mod 2 ^ 160 |},
       {| Stack.value := rest |})
    end.

  Fixpoint list_set {A : Type} (l : list A) (n : nat) (v : A) : list A :=
    match l, n with
    | [], _ => []
    | _ :: rest, O => v :: rest
    | x :: rest, S n => x :: list_set rest n v
    end.

  Definition exchange (self : Self) (n m : usize) : bool * Self :=
    let stack_list := self.(Stack.value) in
    let len := Z.of_nat (List.length stack_list) in
    let nm := (i[n] + i[m])%Z in
    if nm <? len then
      let n_nat := Z.to_nat i[n] in
      let nm_nat := Z.to_nat nm in
      match List.nth_error stack_list n_nat,
            List.nth_error stack_list nm_nat with
      | Some vn, Some vnm =>
        let stack' := list_set (list_set stack_list n_nat vnm) nm_nat vn in
        (true, {| Stack.value := stack' |})
      | _, _ => (false, self)
      end
    else
      (false, self).

  Definition dup (self : Self) (n : usize) : bool * Self :=
    let len := Z.of_nat (List.length self.(Stack.value)) in
    if (0 <? i[n]) && (i[n] <=? len) && (len <? 1024) then
      match List.nth_error self.(Stack.value) (Z.to_nat (i[n] - 1)) with
      | Some value => (true, {| Stack.value := value :: self.(Stack.value) |})
      | None => (false, self)
      end
    else
      (false, self).

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
      Self :=
    self
      <| Control.next_action := Some action |>
      <| Control.instruction_result := Some result |>.

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
  Definition Self : Set := SpecId.t.

  Parameter is_static : Self -> bool.
  Parameter is_eof : Self -> bool.
  Parameter is_eof_init : Self -> bool.
  Definition spec_id (self : Self) : SpecId.t := self.

  Instance I : RuntimeFlag.C WIRE_types.(InterpreterTypes.Types.RuntimeFlag) := {
    RuntimeFlag.is_static := is_static;
    RuntimeFlag.is_eof := is_eof;
    RuntimeFlag.is_eof_init := is_eof_init;
    RuntimeFlag.spec_id := spec_id;
  }.
End RuntimeFlag.
Export (hints) RuntimeFlag.

Module MemoryTrait.
  Definition Self : Set := Memory.t.
  Definition Synthetic : Set := MemorySlice.t.
  Definition Synthetic1 : Set := MemorySlice.t.

  Definition set_data (self : Self) (memory_offset data_offset len : usize) (data : list u8) : Self :=
    Memory.set_data self memory_offset data_offset len data.

  Definition set (self : Self) (memory_offset : usize) (data : list u8) : Self :=
    Memory.set self memory_offset data.

  Definition size (self : Self) : usize :=
    Memory.size self.

  Definition copy (self : Self) (dst src len : usize) : Self :=
    Memory.copy self dst src len.

  Definition slice (self : Self) (range : Range.t usize) : Synthetic :=
    Memory.slice self range.(Range.start) (range.(Range.end_) -i range.(Range.start)).

  Definition slice_len (self : Self) (offset len : usize) : Synthetic1 :=
    Memory.slice self offset len.

  Definition resize (self : Self) (new_size : usize) : bool * Self :=
    (true, Memory.resize self new_size).

  Instance I : MemoryTrait.C Self Synthetic Synthetic1 := {|
    simulate.interpreter_types.MemoryTrait.set_data := set_data;
    simulate.interpreter_types.MemoryTrait.set := set;
    simulate.interpreter_types.MemoryTrait.size := size;
    simulate.interpreter_types.MemoryTrait.copy := copy;
    simulate.interpreter_types.MemoryTrait.slice := slice;
    simulate.interpreter_types.MemoryTrait.Deref_for_Synthetic := MemorySlice.Deref_I;
    simulate.interpreter_types.MemoryTrait.slice_len := slice_len;
    simulate.interpreter_types.MemoryTrait.Deref_for_Synthetic1 := MemorySlice.Deref_I;
    simulate.interpreter_types.MemoryTrait.resize := resize;
  |}.
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
