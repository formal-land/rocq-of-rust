Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.ops.links.range.
Require Import revm.revm_bytecode.eof.links.types_section.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import ruint.links.lib.

Module Immediates.
  Class C (Self : Set) `{Link Self} : Set := {
    (* fn read_i16(&self) -> i16; *)
    read_i16 (self : Self) : i16;
    (* fn read_u16(&self) -> u16; *)
    read_u16 (self : Self) : u16;
    (* fn read_i8(&self) -> i8; *)
    read_i8 (self : Self) : i8;
    (* fn read_u8(&self) -> u8; *)
    read_u8 (self : Self) : u8;
    (* fn read_offset_i16(&self, offset: isize) -> i16; *)
    read_offset_i16 (self : Self) (offset : isize) : i16;
    (* fn read_offset_u16(&self, offset: isize) -> u16; *)
    read_offset_u16 (self : Self) (offset : isize) : u16;
    (* fn read_slice(&self, len: usize) -> &[u8]; *)
    read_slice (len : usize) : RefStub.t Self (list u8);
  }.

  Module Eq.
    Class t
        (WIRE : Set) {WIRE_types : InterpreterTypes.Types.t}
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        `{!Immediates.Run WIRE_types.(InterpreterTypes.Types.Bytecode)}
        (I : C WIRE_types.(InterpreterTypes.Types.Bytecode)) :
        Prop := {
      read_i16
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_bytecode
        |} in
        {{
          SimulateM.eval_f
            (Immediates.run_read_i16 ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (read_i16 interpreter.(Interpreter.bytecode)),
            (interpreter :: stack)%stack
          )
        }};
      read_u16
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_bytecode
        |} in
        {{
          SimulateM.eval_f
            (Immediates.run_read_u16 ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (read_u16 interpreter.(Interpreter.bytecode)),
            (interpreter :: stack)%stack
          )
        }};
      read_i8
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_bytecode
        |} in
        {{
          SimulateM.eval_f
            (Immediates.run_read_i8 ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (read_i8 interpreter.(Interpreter.bytecode)),
            (interpreter :: stack)%stack
          )
        }};
      read_u8
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_bytecode
        |} in
        {{
          SimulateM.eval_f
            (Immediates.run_read_u8 ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (read_u8 interpreter.(Interpreter.bytecode)),
            (interpreter :: stack)%stack
          )
        }};
      read_offset_i16
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t)
        (offset : isize) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_bytecode
        |} in
        {{
          SimulateM.eval_f
            (Immediates.run_read_offset_i16 ref_self offset)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (read_offset_i16 interpreter.(Interpreter.bytecode) offset),
            (interpreter :: stack)%stack
          )
        }};
      read_offset_u16
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t)
        (offset : isize) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_bytecode
        |} in
        {{
          SimulateM.eval_f
            (Immediates.run_read_offset_u16 ref_self offset)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (read_offset_u16 interpreter.(Interpreter.bytecode) offset),
            (interpreter :: stack)%stack
          )
        }};
      read_slice
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t)
        (len : usize) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_bytecode
        |} in
        {{
          SimulateM.eval_f
            (Immediates.run_read_slice ref_self len)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (RefStub.apply ref_self (read_slice len)),
            (interpreter :: stack)%stack
          )
        }};
    }.
  End Eq.
End Immediates.

Module LegacyBytecode.
  Class C (Self : Set) `{Link Self} : Set := {
    (* fn bytecode_len(&self) -> usize; *)
    bytecode_len (self : Self) : usize;
    (* fn bytecode_slice(&self) -> &[u8]; *)
    bytecode_slice : RefStub.t Self (list u8);
  }.

  Module Eq.
    Class t
        (WIRE : Set) {WIRE_types : InterpreterTypes.Types.t}
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        `{!links.interpreter_types.LegacyBytecode.Run WIRE_types.(InterpreterTypes.Types.Bytecode)}
        (I : C WIRE_types.(InterpreterTypes.Types.Bytecode)) :
        Prop := {
      bytecode_len
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_bytecode
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.LegacyBytecode.run_bytecode_len ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (I.(bytecode_len) interpreter.(Interpreter.bytecode)),
            (interpreter :: stack)%stack
          )
        }};
      bytecode_slice
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_bytecode
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.LegacyBytecode.run_bytecode_slice ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (RefStub.apply ref_self I.(bytecode_slice)),
            (interpreter :: stack)%stack
          )
        }};
    }.
  End Eq.
End LegacyBytecode.

Module Jumps.
  Class C (Self : Set) `{Link Self} : Set := {
    (* fn relative_jump(&mut self, offset: isize); *)
    relative_jump (self : Self) (offset : isize) : Self;
    (* fn absolute_jump(&mut self, offset: usize); *)
    absolute_jump (self : Self) (offset : usize) : Self;
    (* fn is_valid_legacy_jump(&mut self, offset: usize) -> bool; *)
    is_valid_legacy_jump (self : Self) (offset : usize) : bool * Self;
    (* fn pc(&self) -> usize; *)
    pc (self : Self) : usize;
    (* fn opcode(&self) -> u8; *)
    opcode (self : Self) : u8;
  }.

  Module Eq.
    Class t
        (WIRE : Set) {WIRE_types : InterpreterTypes.Types.t}
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        `{!links.interpreter_types.Jumps.Run WIRE_types.(InterpreterTypes.Types.Bytecode)}
        (I : C WIRE_types.(InterpreterTypes.Types.Bytecode)) :
        Prop := {
      relative_jump
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t)
        (offset : isize) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_bytecode
        |} in
        let bytecode' := I.(relative_jump) interpreter.(Interpreter.bytecode) offset in
        {{
          SimulateM.eval_f
            (links.interpreter_types.Jumps.run_relative_jump ref_self offset)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success tt,
            (interpreter <| Interpreter.bytecode := bytecode' |> :: stack_rest)%stack
          )
        }};
      absolute_jump
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t)
        (offset : usize) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_bytecode
        |} in
        let bytecode' := I.(absolute_jump) interpreter.(Interpreter.bytecode) offset in
        {{
          SimulateM.eval_f
            (links.interpreter_types.Jumps.run_absolute_jump ref_self offset)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success tt,
            (interpreter <| Interpreter.bytecode := bytecode' |> :: stack_rest)%stack
          )
        }};
      is_valid_legacy_jump
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t)
        (offset : usize) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_bytecode
        |} in
        let result_self := I.(is_valid_legacy_jump) interpreter.(Interpreter.bytecode) offset in
        {{
          SimulateM.eval_f
            (links.interpreter_types.Jumps.run_is_valid_legacy_jump ref_self offset)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (fst result_self),
            (interpreter <| Interpreter.bytecode := snd result_self |> :: stack_rest)%stack
          )
        }};
      pc
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_bytecode
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.Jumps.run_pc ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (I.(pc) interpreter.(Interpreter.bytecode)),
            (interpreter :: stack)%stack
          )
        }};
      opcode
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_bytecode
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.Jumps.run_opcode ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (I.(opcode) interpreter.(Interpreter.bytecode)),
            (interpreter :: stack)%stack
          )
        }};
    }.
  End Eq.
End Jumps.

Module EofData.
  Class C (Self : Set) `{Link Self} : Set := {
    (* fn data(&self) -> &[u8]; *)
    data : RefStub.t Self (list u8);
    (* fn data_slice(&self, offset: usize, len: usize) -> &[u8]; *)
    data_slice (offset len : usize) : RefStub.t Self (list u8);
    (* fn data_size(&self) -> usize; *)
    data_size (self : Self) : usize;
  }.

  Module Eq.
    Class t
        (WIRE : Set) {WIRE_types : InterpreterTypes.Types.t}
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        `{!links.interpreter_types.EofData.Run WIRE_types.(InterpreterTypes.Types.Bytecode)}
        (I : C WIRE_types.(InterpreterTypes.Types.Bytecode)) :
        Prop := {
      data
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_bytecode
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.EofData.run_data ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (RefStub.apply ref_self I.(data)),
            (interpreter :: stack)%stack
          )
        }};
      data_slice
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t)
        (offset len : usize) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_bytecode
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.EofData.run_data_slice ref_self offset len)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (RefStub.apply ref_self (I.(data_slice) offset len)),
            (interpreter :: stack)%stack
          )
        }};
      data_size
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_bytecode
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.EofData.run_data_size ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (I.(data_size) interpreter.(Interpreter.bytecode)),
            (interpreter :: stack)%stack
          )
        }};
    }.
  End Eq.
End EofData.

Module EofContainer.
  Class C (Self : Set) `{Link Self} : Set := {
    (* fn eof_container(&self, index: usize) -> Option<&Bytes>; *)
    eof_container (self : Self) (index : usize) : option Bytes.t;
  }.

  Module Eq.
    Class t
        (WIRE : Set) {WIRE_types : InterpreterTypes.Types.t}
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        `{!links.interpreter_types.EofContainer.Run WIRE_types.(InterpreterTypes.Types.Bytecode)}
        (I : C WIRE_types.(InterpreterTypes.Types.Bytecode)) :
        Prop := {
      eof_container
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t)
        (index : usize) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_bytecode
        |} in
        let result := I.(eof_container) interpreter.(Interpreter.bytecode) index in
        {{
          SimulateM.eval_f
            (links.interpreter_types.EofContainer.run_eof_container ref_self index)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (option_map (fun _ => make_ref 0) result),
            (interpreter :: stack)%stack
          )
        }};
    }.
  End Eq.
End EofContainer.

Module EofCodeInfo.
  Class C (Self : Set) `{Link Self} : Set := {
    (* fn code_section_info(&self, idx: usize) -> Option<&TypesSection>; *)
    code_section_info (self : Self) (idx : usize) : option TypesSection.t;
    (* fn code_section_pc(&self, idx: usize) -> Option<usize>; *)
    code_section_pc (self : Self) (idx : usize) : option usize;
  }.

  Module Eq.
    Class t
        (WIRE : Set) {WIRE_types : InterpreterTypes.Types.t}
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        `{!links.interpreter_types.EofCodeInfo.Run WIRE_types.(InterpreterTypes.Types.Bytecode)}
        (I : C WIRE_types.(InterpreterTypes.Types.Bytecode)) :
        Prop := {
      code_section_info
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t)
        (idx : usize) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_bytecode
        |} in
        let result := I.(code_section_info) interpreter.(Interpreter.bytecode) idx in
        {{
          SimulateM.eval_f
            (links.interpreter_types.EofCodeInfo.run_code_section_info ref_self idx)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (option_map (fun _ => make_ref 0) result),
            (interpreter :: stack)%stack
          )
        }};
      code_section_pc
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t)
        (idx : usize) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_bytecode
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.EofCodeInfo.run_code_section_pc ref_self idx)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (I.(code_section_pc) interpreter.(Interpreter.bytecode) idx),
            (interpreter :: stack)%stack
          )
        }};
    }.
  End Eq.
End EofCodeInfo.

Module InputTraits.
  Class C (Self : Set) `{Link Self} : Set := {
    (* fn target_address(&self) -> Address; *)
    target_address (self : Self) : Address.t;
    (* fn caller_address(&self) -> Address; *)
    caller_address (self : Self) : Address.t;
    (* fn input(&self) -> &[u8]; *)
    input : RefStub.t Self (list u8);
    (* fn call_value(&self) -> U256; *)
    call_value (self : Self) : aliases.U256.t;
  }.

  Module Eq.
    Class t
        (WIRE : Set) {WIRE_types : InterpreterTypes.Types.t}
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        `{!InputsTrait.Run WIRE_types.(InterpreterTypes.Types.Input)}
        (I : C WIRE_types.(InterpreterTypes.Types.Input)) :
        Prop := {
      target_address
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_input
        |} in
        {{
          SimulateM.eval_f
            (InputsTrait.run_target_address ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (I.(target_address) interpreter.(Interpreter.input)),
            (interpreter :: stack)%stack
          )
        }};
      caller_address
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_input
        |} in
        {{
          SimulateM.eval_f
            (InputsTrait.run_caller_address ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (I.(caller_address) interpreter.(Interpreter.input)),
            (interpreter :: stack)%stack
          )
        }};
      input
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_input
        |} in
        {{
          SimulateM.eval_f
            (InputsTrait.run_input ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (RefStub.apply ref_self I.(input)),
            (interpreter :: stack)%stack
          )
        }};
      call_value
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_input
        |} in
        {{
          SimulateM.eval_f
            (InputsTrait.run_call_value ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (I.(call_value) interpreter.(Interpreter.input)),
            (interpreter :: stack)%stack
          )
        }};
    }.
  End Eq.
End InputTraits.

Module StackTrait.
  Class C (Self : Set) `{Link Self} : Type := {
    (* fn len(&self) -> usize; *)
    len (self : Self) : usize;
    (* fn is_empty(&self) -> bool; *)
    is_empty (self : Self) : bool;
    (* fn push(&mut self, value: U256) -> bool; *)
    push (self : Self) (value : aliases.U256.t) : bool * Self;
    (* fn push_b256(&mut self, value: B256) -> bool; *)
    push_b256 (self : Self) (value : aliases.B256.t) : bool * Self;
    (* fn popn<const N: usize>(&mut self) -> Option<[U256; N]>; *)
    popn (N : usize) (self : Self) : option (array.t aliases.U256.t N) * Self;
    (* fn popn_top<const POPN: usize>(&mut self) -> Option<([U256; POPN], &mut U256)>; *)
    popn_top (POPN : usize) (self : Self) :
      option (array.t aliases.U256.t POPN * RefStub.t Self aliases.U256.t) * Self;
    (* fn top(&mut self) -> Option<&mut U256>; *)
    top (self : Self) : option (RefStub.t Self aliases.U256.t) * Self;
    (* fn pop(&mut self) -> Option<U256>; *)
    pop (self : Self) : option aliases.U256.t * Self;
    (* fn pop_address(&mut self) -> Option<Address>; *)
    pop_address (self : Self) : option Address.t * Self;
    (* fn exchange(&mut self, n: usize, m: usize) -> bool; *)
    exchange (self : Self) (n m : usize) : bool * Self;
    (* fn dup(&mut self, n: usize) -> bool; *)
    dup (self : Self) (n : usize) : bool * Self;
  }.

  Module Eq.
    Class t
        (WIRE : Set) {WIRE_types : InterpreterTypes.Types.t}
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        `{!links.interpreter_types.StackTrait.Run WIRE_types.(InterpreterTypes.Types.Stack)}
        (I : C WIRE_types.(InterpreterTypes.Types.Stack)) :
        Prop := {
      len
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_stack
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.StackTrait.run_len ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (I.(len) interpreter.(Interpreter.stack)),
            (interpreter :: stack)%stack
          )
        }};
      is_empty
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_stack
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.StackTrait.run_is_empty ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (I.(is_empty) interpreter.(Interpreter.stack)),
            (interpreter :: stack)%stack
          )
        }};
      push
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t)
        (value : aliases.U256.t) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_stack
        |} in
        let result_self := I.(push) interpreter.(Interpreter.stack) value in
        {{
          SimulateM.eval_f
            (links.interpreter_types.StackTrait.run_push ref_self value)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (fst result_self),
            (interpreter <| Interpreter.stack := snd result_self |> :: stack_rest)%stack
          )
        }};
      push_b256
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t)
        (value : aliases.B256.t) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_stack
        |} in
        let result_self := I.(push_b256) interpreter.(Interpreter.stack) value in
        {{
          SimulateM.eval_f
            (links.interpreter_types.StackTrait.run_push_b256 ref_self value)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (fst result_self),
            (interpreter <| Interpreter.stack := snd result_self |> :: stack_rest)%stack
          )
        }};
      popn
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t)
        (N : usize) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_stack
        |} in
        let result_self := I.(popn) N interpreter.(Interpreter.stack) in
        {{
          SimulateM.eval_f
            (links.interpreter_types.StackTrait.run_popn N ref_self)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (fst result_self),
            (interpreter <| Interpreter.stack := snd result_self |> :: stack_rest)%stack
          )
        }};
      popn_top
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t)
        (POPN : usize) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_stack
        |} in
        let result_self := I.(popn_top) POPN interpreter.(Interpreter.stack) in
        let result :=
          match fst result_self with
          | Some (a, stub) => Some (a, RefStub.apply ref_self stub)
          | None => None
          end in
        {{
          SimulateM.eval_f
            (links.interpreter_types.StackTrait.run_popn_top POPN ref_self)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success result,
            (interpreter <| Interpreter.stack := snd result_self |> :: stack_rest)%stack
          )
        }};
      top
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_stack
        |} in
        let result_self := I.(top) interpreter.(Interpreter.stack) in
        let result :=
          match fst result_self with
          | Some stub => Some (RefStub.apply ref_self stub)
          | None => None
          end in
        {{
          SimulateM.eval_f
            (links.interpreter_types.StackTrait.run_top ref_self)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success result,
            (interpreter <| Interpreter.stack := snd result_self |> :: stack_rest)%stack
          )
        }};
      pop
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_stack
        |} in
        let result_self := I.(pop) interpreter.(Interpreter.stack) in
        {{
          SimulateM.eval_f
            (links.interpreter_types.StackTrait.run_pop ref_self)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (fst result_self),
            (interpreter <| Interpreter.stack := snd result_self |> :: stack_rest)%stack
          )
        }};
      pop_address
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_stack
        |} in
        let result_self := I.(pop_address) interpreter.(Interpreter.stack) in
        {{
          SimulateM.eval_f
            (links.interpreter_types.StackTrait.run_pop_address ref_self)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (fst result_self),
            (interpreter <| Interpreter.stack := snd result_self |> :: stack_rest)%stack
          )
        }};
      exchange
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t)
        (n m : usize) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_stack
        |} in
        let result_self := I.(exchange) interpreter.(Interpreter.stack) n m in
        {{
          SimulateM.eval_f
            (links.interpreter_types.StackTrait.run_exchange ref_self n m)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (fst result_self),
            (interpreter <| Interpreter.stack := snd result_self |> :: stack_rest)%stack
          )
        }};
      dup
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t)
        (n : usize) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_stack
        |} in
        let result_self := I.(dup) interpreter.(Interpreter.stack) n in
        {{
          SimulateM.eval_f
            (links.interpreter_types.StackTrait.run_dup ref_self n)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (fst result_self),
            (interpreter <| Interpreter.stack := snd result_self |> :: stack_rest)%stack
          )
        }};
    }.
  End Eq.
End StackTrait.

Module LoopControl.
  Class C (Self : Set) `{Link Self} : Set := {
    (* fn set_instruction_result(&mut self, result: InstructionResult); *)
    set_instruction_result (self : Self) (result : InstructionResult.t) : Self;
    (* fn set_next_action(&mut self, action: InterpreterAction, result: InstructionResult); *)
    set_next_action (self : Self) (action : InterpreterAction.t) (result : InstructionResult.t) : Self;
    (* fn gas(&mut self) -> &mut Gas; *)
    gas : RefStub.t Self Gas.t;
    (* fn instruction_result(&self) -> InstructionResult; *)
    instruction_result (self : Self) : InstructionResult.t;
    (* fn take_next_action(&mut self) -> InterpreterAction; *)
    take_next_action (self : Self) : InterpreterAction.t * Self;
  }.

  Module Eq.
    Class t
        (WIRE : Set) {WIRE_types : InterpreterTypes.Types.t}
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        `{!links.interpreter_types.LoopControl.Run WIRE_types.(InterpreterTypes.Types.Control)}
        (I : C WIRE_types.(InterpreterTypes.Types.Control)) :
        Prop := {
      set_instruction_result
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t)
        (result : InstructionResult.t) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_control
        |} in
        let control' := I.(set_instruction_result) interpreter.(Interpreter.control) result in
        {{
          SimulateM.eval_f
            (links.interpreter_types.LoopControl.run_set_instruction_result ref_self result)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success tt,
            (interpreter <| Interpreter.control := control' |> :: stack_rest)%stack
          )
        }};
      set_next_action
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t)
        (action : InterpreterAction.t)
        (result : InstructionResult.t) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_control
        |} in
        let control' := I.(set_next_action) interpreter.(Interpreter.control) action result in
        {{
          SimulateM.eval_f
            (links.interpreter_types.LoopControl.run_set_next_action ref_self action result)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success tt,
            (interpreter <| Interpreter.control := control' |> :: stack_rest)%stack
          )
        }};
      gas
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_control
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.LoopControl.run_gas ref_self)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (RefStub.apply ref_self I.(gas)),
            (interpreter :: stack_rest)%stack
          )
        }};
      instruction_result
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_control
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.LoopControl.run_instruction_result ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (I.(instruction_result) interpreter.(Interpreter.control)),
            (interpreter :: stack)%stack
          )
        }};
      take_next_action
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_control
        |} in
        let result_self := I.(take_next_action) interpreter.(Interpreter.control) in
        {{
          SimulateM.eval_f
            (links.interpreter_types.LoopControl.run_take_next_action ref_self)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (fst result_self),
            (interpreter <| Interpreter.control := snd result_self |> :: stack_rest)%stack
          )
        }};
    }.
  End Eq.
End LoopControl.

Module RuntimeFlag.
  Class C (Self : Set) `{Link Self} : Set := {
    (* fn is_static(&self) -> bool; *)
    is_static (self : Self) : bool;
    (* fn is_eof(&self) -> bool; *)
    is_eof (self : Self) : bool;
    (* fn is_eof_init(&self) -> bool; *)
    is_eof_init (self : Self) : bool;
    (* fn spec_id(&self) -> SpecId; *)
    spec_id (self : Self) : SpecId.t;
  }.

  Module Eq.
    Class t
        (WIRE : Set) {WIRE_types : InterpreterTypes.Types.t}
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        `{!links.interpreter_types.RuntimeFlag.Run WIRE_types.(InterpreterTypes.Types.RuntimeFlag)}
        (I : C WIRE_types.(InterpreterTypes.Types.RuntimeFlag)) :
        Prop := {
      is_static
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_runtime_flag
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.RuntimeFlag.run_is_static ref_self)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (I.(is_static) interpreter.(Interpreter.runtime_flag)),
            (interpreter :: stack_rest)%stack
          )
        }};
      is_eof
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_runtime_flag
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.RuntimeFlag.run_is_eof ref_self)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (I.(is_eof) interpreter.(Interpreter.runtime_flag)),
            (interpreter :: stack_rest)%stack
          )
        }};
      is_eof_init
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_runtime_flag
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.RuntimeFlag.run_is_eof_init ref_self)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (I.(is_eof_init) interpreter.(Interpreter.runtime_flag)),
            (interpreter :: stack_rest)%stack
          )
        }};
      spec_id
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_runtime_flag
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.RuntimeFlag.run_spec_id ref_self)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (I.(spec_id) interpreter.(Interpreter.runtime_flag)),
            (interpreter :: stack_rest)%stack
          )
        }};
    }.
  End Eq.
End RuntimeFlag.

Module MemoryTrait.
  Class C (Self Synthetic Synthetic1 : Set) `{Link Self} `{Link Synthetic} `{Link Synthetic1} : Set := {
    (* fn set_data(&mut self, memory_offset: usize, data_offset: usize, len: usize, data: &[u8]); *)
    set_data (self : Self) (memory_offset data_offset len : usize) (data : list u8) : Self;
    (* fn set(&mut self, memory_offset: usize, data: &[u8]); *)
    set (self : Self) (memory_offset : usize) (data : list u8) : Self;
    (* fn size(&self) -> usize; *)
    size (self : Self) : usize;
    (* fn copy(&mut self, destination: usize, source: usize, len: usize); *)
    copy (self : Self) (destination source len : usize) : Self;
    (* fn slice(&self, range: Range<usize>) -> impl Deref<Target = [u8]> + '_; *)
    slice (self : Self) (range : range.Range.t usize) : Synthetic;
    (* fn slice_len(&self, offset: usize, len: usize) -> impl Deref<Target = [u8]> + '_; *)
    slice_len (self : Self) (offset len : usize) : Synthetic1;
    (* fn resize(&mut self, new_size: usize) -> bool; *)
    resize (self : Self) (new_size : usize) : bool * Self;
  }.

  Module Eq.
    Class t
        (WIRE : Set) {WIRE_types : InterpreterTypes.Types.t}
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        `{!links.interpreter_types.MemoryTrait.Run
            WIRE_types.(InterpreterTypes.Types.Memory)
            WIRE_types.(InterpreterTypes.Types.Memory_Synthetic)
            WIRE_types.(InterpreterTypes.Types.Memory_Synthetic1)}
        (I : C
          WIRE_types.(InterpreterTypes.Types.Memory)
          WIRE_types.(InterpreterTypes.Types.Memory_Synthetic)
          WIRE_types.(InterpreterTypes.Types.Memory_Synthetic1)) :
        Prop := {
      set_data
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t)
        (memory_offset data_offset len : usize)
        (data : list u8) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_memory
        |} in
        let memory' := I.(set_data) interpreter.(Interpreter.memory) memory_offset data_offset len data in
        {{
          SimulateM.eval_f
            (links.interpreter_types.MemoryTrait.run_set_data ref_self memory_offset data_offset len (Ref.immediate _ data))
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success tt,
            (interpreter <| Interpreter.memory := memory' |> :: stack_rest)%stack
          )
        }};
      set
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t)
        (memory_offset : usize)
        (data : list u8) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_memory
        |} in
        let memory' := I.(set) interpreter.(Interpreter.memory) memory_offset data in
        {{
          SimulateM.eval_f
            (links.interpreter_types.MemoryTrait.run_set ref_self memory_offset (Ref.immediate _ data))
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success tt,
            (interpreter <| Interpreter.memory := memory' |> :: stack_rest)%stack
          )
        }};
      size
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_memory
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.MemoryTrait.run_size ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (I.(size) interpreter.(Interpreter.memory)),
            (interpreter :: stack)%stack
          )
        }};
      copy
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t)
        (destination source len : usize) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_memory
        |} in
        let memory' := I.(copy) interpreter.(Interpreter.memory) destination source len in
        {{
          SimulateM.eval_f
            (links.interpreter_types.MemoryTrait.run_copy ref_self destination source len)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success tt,
            (interpreter <| Interpreter.memory := memory' |> :: stack_rest)%stack
          )
        }};
      slice
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t)
        (range : range.Range.t usize) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_memory
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.MemoryTrait.run_slice ref_self range)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (I.(slice) interpreter.(Interpreter.memory) range),
            (interpreter :: stack)%stack
          )
        }};
      slice_len
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t)
        (offset len : usize) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_memory
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.MemoryTrait.run_slice_len ref_self offset len)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (I.(slice_len) interpreter.(Interpreter.memory) offset len),
            (interpreter :: stack)%stack
          )
        }};
      resize
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t)
        (new_size : usize) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_memory
        |} in
        let result_self := I.(resize) interpreter.(Interpreter.memory) new_size in
        {{
          SimulateM.eval_f
            (links.interpreter_types.MemoryTrait.run_resize ref_self new_size)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (fst result_self),
            (interpreter <| Interpreter.memory := snd result_self |> :: stack_rest)%stack
          )
        }};
    }.
  End Eq.
End MemoryTrait.

Module SubRoutineStack.
  Class C (Self : Set) `{Link Self} : Set := {
    (* fn len(&self) -> usize; *)
    len (self : Self) : usize;
    (* fn is_empty(&self) -> bool; *)
    is_empty (self : Self) : bool;
    (* fn routine_idx(&self) -> usize; *)
    routine_idx (self : Self) : usize;
    (* fn set_routine_idx(&mut self, idx: usize); *)
    set_routine_idx (self : Self) (idx : usize) : Self;
    (* fn push(&mut self, old_program_counter: usize, new_idx: usize) -> bool; *)
    push (self : Self) (old_program_counter new_idx : usize) : bool * Self;
    (* fn pop(&mut self) -> Option<usize>; *)
    pop (self : Self) : option usize * Self;
  }.

  Module Eq.
    Class t
        (WIRE : Set) {WIRE_types : InterpreterTypes.Types.t}
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        `{!links.interpreter_types.SubRoutineStack.Run WIRE_types.(InterpreterTypes.Types.SubRoutineStack)}
        (I : C WIRE_types.(InterpreterTypes.Types.SubRoutineStack)) :
        Prop := {
      len
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_sub_routine
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.SubRoutineStack.run_len ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (I.(len) interpreter.(Interpreter.sub_routine)),
            (interpreter :: stack)%stack
          )
        }};
      is_empty
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_sub_routine
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.SubRoutineStack.run_is_empty ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (I.(is_empty) interpreter.(Interpreter.sub_routine)),
            (interpreter :: stack)%stack
          )
        }};
      routine_idx
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_sub_routine
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.SubRoutineStack.run_routine_idx ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (I.(routine_idx) interpreter.(Interpreter.sub_routine)),
            (interpreter :: stack)%stack
          )
        }};
      set_routine_idx
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t)
        (idx : usize) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_sub_routine
        |} in
        let sub_routine' := I.(set_routine_idx) interpreter.(Interpreter.sub_routine) idx in
        {{
          SimulateM.eval_f
            (links.interpreter_types.SubRoutineStack.run_set_routine_idx ref_self idx)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success tt,
            (interpreter <| Interpreter.sub_routine := sub_routine' |> :: stack_rest)%stack
          )
        }};
      push
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t)
        (old_program_counter new_idx : usize) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_sub_routine
        |} in
        let result_self := I.(push) interpreter.(Interpreter.sub_routine) old_program_counter new_idx in
        {{
          SimulateM.eval_f
            (links.interpreter_types.SubRoutineStack.run_push ref_self old_program_counter new_idx)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (fst result_self),
            (interpreter <| Interpreter.sub_routine := snd result_self |> :: stack_rest)%stack
          )
        }};
      pop
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_sub_routine
        |} in
        let result_self := I.(pop) interpreter.(Interpreter.sub_routine) in
        {{
          SimulateM.eval_f
            (links.interpreter_types.SubRoutineStack.run_pop ref_self)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (fst result_self),
            (interpreter <| Interpreter.sub_routine := snd result_self |> :: stack_rest)%stack
          )
        }};
    }.
  End Eq.
End SubRoutineStack.

Module ReturnData.
  Class C (Self : Set) `{Link Self} : Set := {
    (* fn buffer(&self) -> &[u8]; *)
    buffer : RefStub.t Self (list u8);
    (* fn buffer_mut(&mut self) -> &mut Bytes; *)
    buffer_mut : RefStub.t Self Bytes.t;
  }.

  Module Eq.
    Class t
        (WIRE : Set) {WIRE_types : InterpreterTypes.Types.t}
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        `{!links.interpreter_types.ReturnData.Run WIRE_types.(InterpreterTypes.Types.ReturnData)}
        (I : C WIRE_types.(InterpreterTypes.Types.ReturnData)) :
        Prop := {
      buffer
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack : Stack.t) :
        let ref_interpreter : '& (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self : '& _ := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_return_data
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.ReturnData.run_buffer ref_self)
            (interpreter :: stack)%stack 🌲
          (
            Output.Success (RefStub.apply ref_self I.(buffer)),
            (interpreter :: stack)%stack
          )
        }};
      buffer_mut
        (interpreter : Interpreter.t WIRE WIRE_types)
        (stack_rest : Stack.t) :
        let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_return_data
        |} in
        {{
          SimulateM.eval_f
            (links.interpreter_types.ReturnData.run_buffer_mut ref_self)
            (interpreter :: stack_rest)%stack 🌲
          (
            Output.Success (RefStub.apply ref_self I.(buffer_mut)),
            (interpreter :: stack_rest)%stack
          )
        }};
    }.
  End Eq.
End ReturnData.

Module InterpreterTypes.
  Class C
      (WIRE_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks WIRE_types} :
      Type := {
    (* type Stack: StackTrait; *)
    StackTrait_for_Stack :: StackTrait.C WIRE_types.(InterpreterTypes.Types.Stack);
    (* type Memory: MemoryTrait; *)
    MemoryTrait_for_Memory :: MemoryTrait.C
      WIRE_types.(InterpreterTypes.Types.Memory)
      WIRE_types.(InterpreterTypes.Types.Memory_Synthetic)
      WIRE_types.(InterpreterTypes.Types.Memory_Synthetic1);
    (* type Bytecode: Jumps + Immediates + LegacyBytecode + EofData + EofContainer + EofCodeInfo; *)
    Jumps_for_Bytecode :: Jumps.C WIRE_types.(InterpreterTypes.Types.Bytecode);
    Immediates_for_Bytecode :: Immediates.C WIRE_types.(InterpreterTypes.Types.Bytecode);
    LegacyBytecode_for_Bytecode :: LegacyBytecode.C WIRE_types.(InterpreterTypes.Types.Bytecode);
    EofData_for_Bytecode :: EofData.C WIRE_types.(InterpreterTypes.Types.Bytecode);
    EofContainer_for_Bytecode :: EofContainer.C WIRE_types.(InterpreterTypes.Types.Bytecode);
    EofCodeInfo_for_Bytecode :: EofCodeInfo.C WIRE_types.(InterpreterTypes.Types.Bytecode);
    (* type ReturnData: ReturnData; *)
    ReturnData_for_ReturnData :: ReturnData.C WIRE_types.(InterpreterTypes.Types.ReturnData);
    (* type Input: InputsTrait; *)
    InputsTrait_for_Input :: InputTraits.C WIRE_types.(InterpreterTypes.Types.Input);
    (* type SubRoutineStack: SubRoutineStack; *)
    SubRoutineStack_for_SubRoutineStack :: SubRoutineStack.C WIRE_types.(InterpreterTypes.Types.SubRoutineStack);
    (* type Control: LoopControl; *)
    LoopControl_for_Control :: LoopControl.C WIRE_types.(InterpreterTypes.Types.Control);
    (* type RuntimeFlag: RuntimeFlag; *)
    RuntimeFlag_for_RuntimeFlag :: RuntimeFlag.C WIRE_types.(InterpreterTypes.Types.RuntimeFlag);
  }.

  Module Eq.
    Class t
        (WIRE : Set) (WIRE_types : InterpreterTypes.Types.t)
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
        (I : C WIRE_types) :
        Prop := {
      StackTrait_for_Stack :: StackTrait.Eq.t WIRE I.(StackTrait_for_Stack);
      MemoryTrait_for_Memory :: MemoryTrait.Eq.t WIRE I.(MemoryTrait_for_Memory);
      Jumps_for_Bytecode :: Jumps.Eq.t WIRE I.(Jumps_for_Bytecode);
      Immediates_for_Bytecode :: Immediates.Eq.t WIRE I.(Immediates_for_Bytecode);
      LegacyBytecode_for_Bytecode :: LegacyBytecode.Eq.t WIRE I.(LegacyBytecode_for_Bytecode);
      EofData_for_Bytecode :: EofData.Eq.t WIRE I.(EofData_for_Bytecode);
      EofContainer_for_Bytecode :: EofContainer.Eq.t WIRE I.(EofContainer_for_Bytecode);
      EofCodeInfo_for_Bytecode :: EofCodeInfo.Eq.t WIRE I.(EofCodeInfo_for_Bytecode);
      ReturnData_for_ReturnData : ReturnData.Eq.t WIRE I.(ReturnData_for_ReturnData);
      InputsTrait_for_Input :: InputTraits.Eq.t WIRE I.(InputsTrait_for_Input);
      SubRoutineStack_for_SubRoutineStack :: SubRoutineStack.Eq.t WIRE I.(SubRoutineStack_for_SubRoutineStack);
      LoopControl_for_Control :: LoopControl.Eq.t WIRE I.(LoopControl_for_Control);
      RuntimeFlag_for_RuntimeFlag :: RuntimeFlag.Eq.t WIRE I.(RuntimeFlag_for_RuntimeFlag);
    }.
  End Eq.
  Export (hints) Eq.
End InterpreterTypes.
Export (hints) InterpreterTypes.
