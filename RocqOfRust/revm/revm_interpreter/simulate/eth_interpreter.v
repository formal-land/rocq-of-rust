Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import bytes.links.bytes.
Require Import revm.revm_context_interface.simulate.host_runtime.
Require Import revm.revm_interpreter.interpreter.links.runtime_flags.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.simulate.eth_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.runtime.
Require Import revm.revm_primitives.links.hardfork.


Module InputsImpl.
  Record t : Set := {
    target_address : Address.t;
    bytecode_address : option Address.t;
    caller_address : Address.t;
    input : CallInput.t;
    call_value : aliases.U256.t;
  }.
End InputsImpl.

(** The eight fields of Rust's Interpreter<EthInterpreter>. The instruction
    library's older generic interface has two additional control fields; the
    conversion below confines that compatibility detail to this module. *)
Module EthInterpreter.
  Record t : Set := {
    bytecode : Bytecode.t;
    gas : Gas.t;
    stack : Stack.t;
    return_data : alloy_primitives.bytes.links.mod.Bytes.t;
    memory : Memory.t;
    input : InputsImpl.t;
    runtime_flag : RuntimeFlags.t;
    extend : unit;
  }.
End EthInterpreter.

Module Impl_EthInterpreter.
  Definition new (memory : Memory.t) (code : alloy_primitives.bytes.links.mod.Bytes.t) (inputs : InputsImpl.t)
      (is_static : bool) (spec_id : SpecId.t) (gas_limit : u64) : EthInterpreter.t := {|
    EthInterpreter.bytecode := {| Bytecode.code := code.(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value);
      Bytecode.pc := 0; Bytecode.action := None |};
    EthInterpreter.gas := Impl_Gas.new gas_limit;
    EthInterpreter.stack := {| Stack.value := [] |};
    EthInterpreter.return_data := Impl_Bytes.new;
    EthInterpreter.memory := memory;
    EthInterpreter.input := inputs;
    EthInterpreter.runtime_flag := {| RuntimeFlags.is_static := is_static; RuntimeFlags.spec_id := spec_id |};
    EthInterpreter.extend := tt;
  |}.

  Definition instruction_state (self : EthInterpreter.t) : Interpreter.t WIRE WIRE_types := {|
    Interpreter.bytecode := self.(EthInterpreter.bytecode);
    Interpreter.gas := self.(EthInterpreter.gas);
    Interpreter.stack := self.(EthInterpreter.stack);
    Interpreter.return_data := self.(EthInterpreter.return_data);
    Interpreter.memory := self.(EthInterpreter.memory);
    Interpreter.input := {| Input.target_address := self.(EthInterpreter.input).(InputsImpl.target_address);
      Input.caller_address := self.(EthInterpreter.input).(InputsImpl.caller_address);
      Input.input := self.(EthInterpreter.input).(InputsImpl.input);
      Input.call_value := self.(EthInterpreter.input).(InputsImpl.call_value) |};
    Interpreter.runtime_flag := self.(EthInterpreter.runtime_flag);
    Interpreter.extend := tt;
    Interpreter.sub_routine := tt;
    Interpreter.control := {| Control.gas := Impl_Gas.new 0;
      Control.instruction_result := None; Control.next_action := None |};
  |}.

  Definition from_instruction_state (bytecode_address : option Address.t)
      (state : Interpreter.t WIRE WIRE_types) : EthInterpreter.t := {|
    EthInterpreter.bytecode := state.(Interpreter.bytecode);
    EthInterpreter.gas := state.(Interpreter.gas);
    EthInterpreter.stack := state.(Interpreter.stack);
    EthInterpreter.return_data := state.(Interpreter.return_data);
    EthInterpreter.memory := state.(Interpreter.memory);
    EthInterpreter.input := {| InputsImpl.target_address := state.(Interpreter.input).(Input.target_address);
      InputsImpl.bytecode_address := bytecode_address;
      InputsImpl.caller_address := state.(Interpreter.input).(Input.caller_address);
      InputsImpl.input := state.(Interpreter.input).(Input.input);
      InputsImpl.call_value := state.(Interpreter.input).(Input.call_value) |};
    EthInterpreter.runtime_flag := state.(Interpreter.runtime_flag);
    EthInterpreter.extend := tt;
  |}.

  Definition is_not_end (bytecode : Bytecode.t) : bool :=
    match bytecode.(Bytecode.action) with None => true | Some _ => false end.

  Definition run_plain {H : Set} `{HostRuntime.C H} (fuel : nat)
      (self : EthInterpreter.t) (host : H) :=
    match RuntimeInterpreter.run_plain (IInterpreterTypes := InterpreterTypes.I)
      fuel is_not_end (instruction_state self) host with
    | None => None
    | Some (action, state, host, fuel) => Some (action,
        from_instruction_state self.(EthInterpreter.input).(InputsImpl.bytecode_address) state, host, fuel)
    end.

  (** Child memory is local. Shared-buffer call ranges refer to its parent's
      immutable local buffer; returning leaves the parent's buffer in place. *)
  Definition new_child_context (self : Memory.t) : Memory.t := {|
    Memory.value := []; Memory.shared_buffer := self.(Memory.value);
  |}.

  Lemma instruction_state_roundtrip (self : EthInterpreter.t) :
    from_instruction_state self.(EthInterpreter.input).(InputsImpl.bytecode_address)
      (instruction_state self) = self.
  Proof. destruct self as [bytecode gas stack return_data memory input runtime_flag []].
    destruct input. reflexivity. Qed.
End Impl_EthInterpreter.
