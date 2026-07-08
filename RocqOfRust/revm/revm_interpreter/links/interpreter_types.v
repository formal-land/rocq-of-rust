Require Import links.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.ops.links.deref.
Require Import core.ops.links.range.
Require Import core.links.option.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.

(*
pub trait Immediates {
    fn read_i16(&self) -> i16;
    fn read_u16(&self) -> u16;
    fn read_i8(&self) -> i8;
    fn read_u8(&self) -> u8;
    fn read_offset_i16(&self, offset: isize) -> i16;
    fn read_offset_u16(&self, offset: isize) -> u16;
    fn read_slice(&self, len: usize) -> &[u8];
}
*)
Module Immediates.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_interpreter::interpreter_types::Immediates";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_read_i16 (Self : Set) `{Link Self} : Set := {
    read_i16 : PolymorphicFunction.t;
    read_i16_is_method :: IsTraitMethod.C (trait Self) "read_i16" read_i16;
    run_read_i16 (self : '& Self) :: Run.Trait read_i16 [] [] [ φ self ] i16;
  }.

  Class Method_read_u16 (Self : Set) `{Link Self} : Set := {
    read_u16 : PolymorphicFunction.t;
    read_u16_is_method :: IsTraitMethod.C (trait Self) "read_u16" read_u16;
    run_read_u16 (self : '& Self) :: Run.Trait read_u16 [] [] [ φ self ] u16;
  }.

  Class Method_read_i8 (Self : Set) `{Link Self} : Set := {
    read_i8 : PolymorphicFunction.t;
    read_i8_is_method :: IsTraitMethod.C (trait Self) "read_i8" read_i8;
    run_read_i8 (self : '& Self) :: Run.Trait read_i8 [] [] [ φ self ] i8;
  }.

  Class Method_read_u8 (Self : Set) `{Link Self} : Set := {
    read_u8 : PolymorphicFunction.t;
    read_u8_is_method :: IsTraitMethod.C (trait Self) "read_u8" read_u8;
    run_read_u8 (self : '& Self) :: Run.Trait read_u8 [] [] [ φ self ] u8;
  }.

  Class Method_read_offset_i16 (Self : Set) `{Link Self} : Set := {
    read_offset_i16 : PolymorphicFunction.t;
    read_offset_i16_is_method :: IsTraitMethod.C (trait Self) "read_offset_i16" read_offset_i16;
    run_read_offset_i16 (self : '& Self) (offset : isize) ::
      Run.Trait read_offset_i16 [] [] [ φ self; φ offset ] i16;
  }.

  Class Method_read_offset_u16 (Self : Set) `{Link Self} : Set := {
    read_offset_u16 : PolymorphicFunction.t;
    read_offset_u16_is_method :: IsTraitMethod.C (trait Self) "read_offset_u16" read_offset_u16;
    run_read_offset_u16 (self : '& Self) (offset : isize) ::
      Run.Trait read_offset_u16 [] [] [ φ self; φ offset ] u16;
  }.

  Class Method_read_slice (Self : Set) `{Link Self} : Set := {
    read_slice : PolymorphicFunction.t;
    read_slice_is_method :: IsTraitMethod.C (trait Self) "read_slice" read_slice;
    run_read_slice (self : '& Self) (len : usize) ::
      Run.Trait read_slice [] [] [ φ self; φ len ] ('& (list u8));
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    method_read_i16 :: Method_read_i16 Self;
    method_read_u16 :: Method_read_u16 Self;
    method_read_i8 :: Method_read_i8 Self;
    method_read_u8 :: Method_read_u8 Self;
    method_read_offset_i16 :: Method_read_offset_i16 Self;
    method_read_offset_u16 :: Method_read_offset_u16 Self;
    method_read_slice :: Method_read_slice Self;
  }.
End Immediates.
Export (hints) Immediates.

(*
pub trait InputsTr {
    fn target_address(&self) -> Address;
    fn caller_address(&self) -> Address;
    fn input(&self) -> &CallInput;
    fn call_value(&self) -> U256;
}
*)
Module InputsTrait.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_interpreter::interpreter_types::InputsTr";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_target_address (Self : Set) `{Link Self} : Set := {
    target_address : PolymorphicFunction.t;
    target_address_is_method :: IsTraitMethod.C (trait Self) "target_address" target_address;
    run_target_address (self : '& Self) :: Run.Trait target_address [] [] [ φ self ] Address.t;
  }.

  Class Method_caller_address (Self : Set) `{Link Self} : Set := {
    caller_address : PolymorphicFunction.t;
    caller_address_is_method :: IsTraitMethod.C (trait Self) "caller_address" caller_address;
    run_caller_address (self : '& Self) :: Run.Trait caller_address [] [] [ φ self ] Address.t;
  }.

  Class Method_input (Self : Set) `{Link Self} : Set := {
    input : PolymorphicFunction.t;
    input_is_method :: IsTraitMethod.C (trait Self) "input" input;
    run_input (self : '& Self) :: Run.Trait input [] [] [ φ self ]
      ('& revm.revm_interpreter.interpreter_action.links.call_inputs.CallInput.t);
  }.

  Class Method_call_value (Self : Set) `{Link Self} : Set := {
    call_value : PolymorphicFunction.t;
    call_value_is_method :: IsTraitMethod.C (trait Self) "call_value" call_value;
    run_call_value (self : '& Self) :: Run.Trait call_value [] [] [ φ self ] aliases.U256.t;
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    method_target_address :: Method_target_address Self;
    method_caller_address :: Method_caller_address Self;
    method_input :: Method_input Self;
    method_call_value :: Method_call_value Self;
  }.
End InputsTrait.
Export (hints) InputsTrait.

(*
pub trait LegacyBytecode {
    fn bytecode_len(&self) -> usize;
    fn bytecode_slice(&self) -> &[u8];
}
*)
Module LegacyBytecode.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_interpreter::interpreter_types::LegacyBytecode";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_bytecode_len (Self : Set) `{Link Self} : Set := {
    bytecode_len : PolymorphicFunction.t;
    bytecode_len_is_method :: IsTraitMethod.C (trait Self) "bytecode_len" bytecode_len;
    run_bytecode_len (self : '& Self) :: Run.Trait bytecode_len [] [] [ φ self ] usize;
  }.

  Class Method_bytecode_slice (Self : Set) `{Link Self} : Set := {
    bytecode_slice : PolymorphicFunction.t;
    bytecode_slice_is_method :: IsTraitMethod.C (trait Self) "bytecode_slice" bytecode_slice;
    run_bytecode_slice (self : '& Self) :: Run.Trait bytecode_slice [] [] [ φ self ] ('& (list u8));
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    method_bytecode_len :: Method_bytecode_len Self;
    method_bytecode_slice :: Method_bytecode_slice Self;
  }.
End LegacyBytecode.
Export (hints) LegacyBytecode.

(*
pub trait Jumps {
    fn relative_jump(&mut self, offset: isize);
    fn absolute_jump(&mut self, offset: usize);
    fn is_valid_legacy_jump(&mut self, offset: usize) -> bool;
    fn pc(&self) -> usize;
    fn opcode(&self) -> u8;
}
*)
Module Jumps.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_interpreter::interpreter_types::Jumps";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_relative_jump (Self : Set) `{Link Self} : Set := {
    relative_jump : PolymorphicFunction.t;
    relative_jump_is_method :: IsTraitMethod.C (trait Self) "relative_jump" relative_jump;
    run_relative_jump (self : '&mut Self) (offset : isize) ::
      Run.Trait relative_jump [] [] [ φ self; φ offset ] unit;
  }.

  Class Method_absolute_jump (Self : Set) `{Link Self} : Set := {
    absolute_jump : PolymorphicFunction.t;
    absolute_jump_is_method :: IsTraitMethod.C (trait Self) "absolute_jump" absolute_jump;
    run_absolute_jump (self : '&mut Self) (offset : usize) ::
      Run.Trait absolute_jump [] [] [ φ self; φ offset ] unit;
  }.

  Class Method_is_valid_legacy_jump (Self : Set) `{Link Self} : Set := {
    is_valid_legacy_jump : PolymorphicFunction.t;
    is_valid_legacy_jump_is_method :: IsTraitMethod.C (trait Self) "is_valid_legacy_jump" is_valid_legacy_jump;
    run_is_valid_legacy_jump (self : '&mut Self) (offset : usize) ::
      Run.Trait is_valid_legacy_jump [] [] [ φ self; φ offset ] bool;
  }.

  Class Method_pc (Self : Set) `{Link Self} : Set := {
    pc : PolymorphicFunction.t;
    pc_is_method :: IsTraitMethod.C (trait Self) "pc" pc;
    run_pc (self : '& Self) :: Run.Trait pc [] [] [ φ self ] usize;
  }.

  Class Method_opcode (Self : Set) `{Link Self} : Set := {
    opcode : PolymorphicFunction.t;
    opcode_is_method :: IsTraitMethod.C (trait Self) "opcode" opcode;
    run_opcode (self : '& Self) :: Run.Trait opcode [] [] [ φ self ] u8;
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    method_relative_jump :: Method_relative_jump Self;
    method_absolute_jump :: Method_absolute_jump Self;
    method_is_valid_legacy_jump :: Method_is_valid_legacy_jump Self;
    method_pc :: Method_pc Self;
    method_opcode :: Method_opcode Self;
  }.
End Jumps.
Export (hints) Jumps.

(*
pub trait MemoryTrait {
    fn set_data(&mut self, memory_offset: usize, data_offset: usize, len: usize, data: &[u8]);
    fn set_data_from_global(
        &mut self,
        memory_offset: usize,
        data_offset: usize,
        len: usize,
        data_range: Range<usize>,
    );
    fn set(&mut self, memory_offset: usize, data: &[u8]);
    fn size(&self) -> usize;
    fn copy(&mut self, destination: usize, source: usize, len: usize);
    fn slice(&self, range: Range<usize>) -> impl Deref<Target = [u8]> + '_;
    fn global_slice(&self, range: Range<usize>) -> impl Deref<Target = [u8]> + '_;
    fn slice_len(&self, offset: usize, len: usize) -> impl Deref<Target = [u8]> + '_;
    fn resize(&mut self, new_size: usize) -> bool;
}
*)
Module MemoryTrait.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_interpreter::interpreter_types::MemoryTr";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_set_data (Self : Set) `{Link Self} : Set := {
    set_data : PolymorphicFunction.t;
    set_data_is_method :: IsTraitMethod.C (trait Self) "set_data" set_data;
    run_set_data (self : '&mut Self) (memory_offset data_offset len : usize) (data : '& (list u8)) ::
      Run.Trait set_data [] [] [ φ self; φ memory_offset; φ data_offset; φ len; φ data ] unit;
  }.

  Class Method_set_data_from_global (Self : Set) `{Link Self} : Set := {
    set_data_from_global : PolymorphicFunction.t;
    set_data_from_global_is_method ::
      IsTraitMethod.C (trait Self) "set_data_from_global" set_data_from_global;
    run_set_data_from_global
      (self : '&mut Self) (memory_offset data_offset len : usize) (data_range : range.Range.t usize) ::
      Run.Trait set_data_from_global [] []
        [ φ self; φ memory_offset; φ data_offset; φ len; φ data_range ] unit;
  }.

  Class Method_set (Self : Set) `{Link Self} : Set := {
    set : PolymorphicFunction.t;
    set_is_method :: IsTraitMethod.C (trait Self) "set" set;
    run_set (self : '&mut Self) (memory_offset : usize) (data : '& (list u8)) ::
      Run.Trait set [] [] [ φ self; φ memory_offset; φ data ] unit;
  }.

  Class Method_size (Self : Set) `{Link Self} : Set := {
    size : PolymorphicFunction.t;
    size_is_method :: IsTraitMethod.C (trait Self) "size" size;
    run_size (self : '& Self) :: Run.Trait size [] [] [ φ self ] usize;
  }.

  Class Method_local_memory_offset (Self : Set) `{Link Self} : Set := {
    local_memory_offset : PolymorphicFunction.t;
    local_memory_offset_is_method :: IsTraitMethod.C (trait Self) "local_memory_offset" local_memory_offset;
    run_local_memory_offset (self : '& Self) ::
      Run.Trait local_memory_offset [] [] [ φ self ] usize;
  }.

  Class Method_copy (Self : Set) `{Link Self} : Set := {
    copy : PolymorphicFunction.t;
    copy_is_method :: IsTraitMethod.C (trait Self) "copy" copy;
    run_copy (self : '&mut Self) (destination source len : usize) ::
      Run.Trait copy [] [] [ φ self; φ destination; φ source; φ len ] unit;
  }.

  Class Method_slice (Self Synthetic : Set) `{Link Self} `{Link Synthetic} : Set := {
    slice : PolymorphicFunction.t;
    slice_is_method :: IsTraitMethod.C (trait Self) "slice" slice;
    run_slice (self : '& Self) (range : range.Range.t usize) ::
      Run.Trait slice [] [] [ φ self; φ range ] Synthetic;
  }.

  Class Method_global_slice (Self Synthetic : Set) `{Link Self} `{Link Synthetic} : Set := {
    global_slice : PolymorphicFunction.t;
    global_slice_is_method :: IsTraitMethod.C (trait Self) "global_slice" global_slice;
    run_global_slice (self : '& Self) (range : range.Range.t usize) ::
      Run.Trait global_slice [] [] [ φ self; φ range ] Synthetic;
  }.

  Class Method_slice_len (Self Synthetic : Set) `{Link Self} `{Link Synthetic} : Set := {
    slice_len : PolymorphicFunction.t;
    slice_len_is_method :: IsTraitMethod.C (trait Self) "slice_len" slice_len;
    run_slice_len (self : '& Self) (offset len : usize) ::
      Run.Trait slice_len [] [] [ φ self; φ offset; φ len ] Synthetic;
  }.

  Class Method_resize (Self : Set) `{Link Self} : Set := {
    resize : PolymorphicFunction.t;
    resize_is_method :: IsTraitMethod.C (trait Self) "resize" resize;
    run_resize (self : '&mut Self) (new_size : usize) ::
      Run.Trait resize [] [] [ φ self; φ new_size ] bool;
  }.

  Class Run (Self Synthetic Synthetic1 : Set)
      `{Link Self} `{Link Synthetic} `{Link Synthetic1} :
      Set := {
    method_set_data :: Method_set_data Self;
    method_set_data_from_global :: Method_set_data_from_global Self;
    method_set :: Method_set Self;
    method_size :: Method_size Self;
    method_local_memory_offset :: Method_local_memory_offset Self;
    method_copy :: Method_copy Self;
    Synthetic_IsAssociated :
      IsTraitAssociatedType "revm_interpreter::interpreter_types::MemoryTr" [] [] (Φ Self)
      "{{anon_assoc}}" (Φ Synthetic);
    run_Deref_for_Synthetic :: deref.Deref.Run Synthetic (list u8);
    method_slice :: Method_slice Self Synthetic;
    method_global_slice :: Method_global_slice Self Synthetic;
    Synthetic1_IsAssociated :
      IsTraitAssociatedType "revm_interpreter::interpreter_types::MemoryTr" [] [] (Φ Self)
      "{{synthetic}}'1" (Φ Synthetic1);
    run_Deref_for_Synthetic1 :: deref.Deref.Run Synthetic1 (list u8);
    method_slice_len :: Method_slice_len Self Synthetic;
    method_resize :: Method_resize Self;
  }.
End MemoryTrait.
Export (hints) MemoryTrait.

(*
pub trait EofContainer {
    fn eof_container(&self, index: usize) -> Option<&Bytes>;
}
*)
Module EofContainer.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_interpreter::interpreter_types::EofContainer";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_eof_container (Self : Set) `{Link Self} : Set := {
    eof_container : PolymorphicFunction.t;
    eof_container_is_method :: IsTraitMethod.C (trait Self) "eof_container" eof_container;
    run_eof_container (self : '& Self) (index : usize) ::
      Run.Trait eof_container [] [] [ φ self; φ index ] (option ('& Bytes.t));
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    method_eof_container :: Method_eof_container Self;
  }.
End EofContainer.
Export (hints) EofContainer.

(*
pub trait SubRoutineStack {
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn routine_idx(&self) -> usize;
    fn set_routine_idx(&mut self, idx: usize);
    fn push(&mut self, old_program_counter: usize, new_idx: usize) -> bool;
    fn pop(&mut self) -> Option<usize>;
}
*)
Module SubRoutineStack.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_interpreter::interpreter_types::SubRoutineStack";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_len (Self : Set) `{Link Self} : Set := {
    len : PolymorphicFunction.t;
    len_is_method :: IsTraitMethod.C (trait Self) "len" len;
    run_len (self : '& Self) :: Run.Trait len [] [] [ φ self ] usize;
  }.

  Class Method_is_empty (Self : Set) `{Link Self} : Set := {
    is_empty : PolymorphicFunction.t;
    is_empty_is_method :: IsTraitMethod.C (trait Self) "is_empty" is_empty;
    run_is_empty (self : '& Self) :: Run.Trait is_empty [] [] [ φ self ] bool;
  }.

  Class Method_routine_idx (Self : Set) `{Link Self} : Set := {
    routine_idx : PolymorphicFunction.t;
    routine_idx_is_method :: IsTraitMethod.C (trait Self) "routine_idx" routine_idx;
    run_routine_idx (self : '& Self) :: Run.Trait routine_idx [] [] [ φ self ] usize;
  }.

  Class Method_set_routine_idx (Self : Set) `{Link Self} : Set := {
    set_routine_idx : PolymorphicFunction.t;
    set_routine_idx_is_method :: IsTraitMethod.C (trait Self) "set_routine_idx" set_routine_idx;
    run_set_routine_idx (self : '&mut Self) (idx : usize) ::
      Run.Trait set_routine_idx [] [] [ φ self; φ idx ] unit;
  }.

  Class Method_push (Self : Set) `{Link Self} : Set := {
    push : PolymorphicFunction.t;
    push_is_method :: IsTraitMethod.C (trait Self) "push" push;
    run_push (self : '&mut Self) (old_program_counter new_idx : usize) ::
      Run.Trait push [] [] [ φ self; φ old_program_counter; φ new_idx ] bool;
  }.

  Class Method_pop (Self : Set) `{Link Self} : Set := {
    pop : PolymorphicFunction.t;
    pop_is_method :: IsTraitMethod.C (trait Self) "pop" pop;
    run_pop (self : '&mut Self) :: Run.Trait pop [] [] [ φ self ] (option usize);
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    method_len :: Method_len Self;
    method_is_empty :: Method_is_empty Self;
    method_routine_idx :: Method_routine_idx Self;
    method_set_routine_idx :: Method_set_routine_idx Self;
    method_push :: Method_push Self;
    method_pop :: Method_pop Self;
  }.
End SubRoutineStack.
Export (hints) SubRoutineStack.

(*
pub trait StackTrait {
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn push(&mut self, value: U256) -> bool;
    fn push_b256(&mut self, value: B256) -> bool;
    fn popn<const N: usize>(&mut self) -> Option<[U256; N]>;
    fn popn_top<const POPN: usize>(&mut self) -> Option<([U256; POPN], &mut U256)>;
    fn top(&mut self) -> Option<&mut U256>;
    fn pop(&mut self) -> Option<U256>;
    fn pop_address(&mut self) -> Option<Address>;
    fn exchange(&mut self, n: usize, m: usize) -> bool;
    fn dup(&mut self, n: usize) -> bool;
}
*)
Module StackTrait.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_interpreter::interpreter_types::StackTr";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_len (Self : Set) `{Link Self} : Set := {
    len : PolymorphicFunction.t;
    len_is_method :: IsTraitMethod.C (trait Self) "len" len;
    run_len (self : '& Self) :: Run.Trait len [] [] [ φ self ] usize;
  }.

  Class Method_is_empty (Self : Set) `{Link Self} : Set := {
    is_empty : PolymorphicFunction.t;
    is_empty_is_method :: IsTraitMethod.C (trait Self) "is_empty" is_empty;
    run_is_empty (self : '& Self) :: Run.Trait is_empty [] [] [ φ self ] bool;
  }.

  Class Method_push (Self : Set) `{Link Self} : Set := {
    push : PolymorphicFunction.t;
    push_is_method :: IsTraitMethod.C (trait Self) "push" push;
    run_push (self : '&mut Self) (value : aliases.U256.t) ::
      Run.Trait push [] [] [ φ self; φ value ] bool;
  }.

  Class Method_push_slice (Self : Set) `{Link Self} : Set := {
    push_slice : PolymorphicFunction.t;
    push_slice_is_method :: IsTraitMethod.C (trait Self) "push_slice" push_slice;
    run_push_slice (self : '&mut Self) (slice : '& (list u8)) ::
      Run.Trait push_slice [] [] [ φ self; φ slice ] bool;
  }.

  Class Method_push_b256 (Self : Set) `{Link Self} : Set := {
    push_b256 : PolymorphicFunction.t;
    push_b256_is_method :: IsTraitMethod.C (trait Self) "push_b256" push_b256;
    run_push_b256 (self : '&mut Self) (value : aliases.B256.t) ::
      Run.Trait push_b256 [] [] [ φ self; φ value ] bool;
  }.

  Class Method_popn (Self : Set) `{Link Self} : Set := {
    popn : PolymorphicFunction.t;
    popn_is_method :: IsTraitMethod.C (trait Self) "popn" popn;
    run_popn (N : usize) (self : '&mut Self) ::
      Run.Trait popn [ φ N ] [] [ φ self ] (option (array.t aliases.U256.t N));
  }.

  Class Method_popn_top (Self : Set) `{Link Self} : Set := {
    popn_top : PolymorphicFunction.t;
    popn_top_is_method :: IsTraitMethod.C (trait Self) "popn_top" popn_top;
    run_popn_top (POPN : usize) (self : '&mut Self) ::
      Run.Trait popn_top [ φ POPN ] [] [ φ self ]
        (option (array.t aliases.U256.t POPN * '&mut aliases.U256.t));
  }.

  Class Method_top (Self : Set) `{Link Self} : Set := {
    top : PolymorphicFunction.t;
    top_is_method :: IsTraitMethod.C (trait Self) "top" top;
    run_top (self : '&mut Self) ::
      Run.Trait top [] [ Φ aliases.U256.t ] [ φ self ] (option ('&mut aliases.U256.t));
  }.

  Class Method_pop (Self : Set) `{Link Self} : Set := {
    pop : PolymorphicFunction.t;
    pop_is_method :: IsTraitMethod.C (trait Self) "pop" pop;
    run_pop (self : '&mut Self) ::
      Run.Trait pop [] [ Φ aliases.U256.t ] [ φ self ] (option aliases.U256.t);
  }.

  Class Method_pop_address (Self : Set) `{Link Self} : Set := {
    pop_address : PolymorphicFunction.t;
    pop_address_is_method :: IsTraitMethod.C (trait Self) "pop_address" pop_address;
    run_pop_address (self : '&mut Self) ::
      Run.Trait pop_address [] [ Φ Address.t ] [ φ self ] (option Address.t);
  }.

  Class Method_exchange (Self : Set) `{Link Self} : Set := {
    exchange : PolymorphicFunction.t;
    exchange_is_method :: IsTraitMethod.C (trait Self) "exchange" exchange;
    run_exchange (self : '&mut Self) (n m : usize) ::
      Run.Trait exchange [] [] [ φ self; φ n; φ m ] bool;
  }.

  Class Method_dup (Self : Set) `{Link Self} : Set := {
    dup : PolymorphicFunction.t;
    dup_is_method :: IsTraitMethod.C (trait Self) "dup" dup;
    run_dup (self : '&mut Self) (n : usize) ::
      Run.Trait dup [] [] [ φ self; φ n ] bool;
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    method_len :: Method_len Self;
    method_is_empty :: Method_is_empty Self;
    method_push :: Method_push Self;
    method_push_slice :: Method_push_slice Self;
    method_push_b256 :: Method_push_b256 Self;
    method_popn :: Method_popn Self;
    method_popn_top :: Method_popn_top Self;
    method_top :: Method_top Self;
    method_pop :: Method_pop Self;
    method_pop_address :: Method_pop_address Self;
    method_exchange :: Method_exchange Self;
    method_dup :: Method_dup Self;
  }.
End StackTrait.
Export (hints) StackTrait.

(*
pub trait EofData {
    fn data(&self) -> &[u8];
    fn data_slice(&self, offset: usize, len: usize) -> &[u8];
    fn data_size(&self) -> usize;
}
*)
Module EofData.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_interpreter::interpreter_types::EofData";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_data (Self : Set) `{Link Self} : Set := {
    data : PolymorphicFunction.t;
    data_is_method :: IsTraitMethod.C (trait Self) "data" data;
    run_data (self : '& Self) :: Run.Trait data [] [] [ φ self ] ('& (list u8));
  }.

  Class Method_data_slice (Self : Set) `{Link Self} : Set := {
    data_slice : PolymorphicFunction.t;
    data_slice_is_method :: IsTraitMethod.C (trait Self) "data_slice" data_slice;
    run_data_slice (self : '& Self) (offset len : usize) ::
      Run.Trait data_slice [] [] [ φ self; φ offset; φ len ] ('& (list u8));
  }.

  Class Method_data_size (Self : Set) `{Link Self} : Set := {
    data_size : PolymorphicFunction.t;
    data_size_is_method :: IsTraitMethod.C (trait Self) "data_size" data_size;
    run_data_size (self : '& Self) :: Run.Trait data_size [] [] [ φ self ] usize;
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    method_data :: Method_data Self;
    method_data_slice :: Method_data_slice Self;
    method_data_size :: Method_data_size Self;
  }.
End EofData.
Export (hints) EofData.

(*
pub trait ReturnData {
    fn buffer(&self) -> &Bytes;
    fn buffer_mut(&mut self) -> &mut Bytes;
}
*)
Module ReturnData.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_interpreter::interpreter_types::ReturnData";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_buffer (Self : Set) `{Link Self} : Set := {
    buffer : PolymorphicFunction.t;
    buffer_is_method :: IsTraitMethod.C (trait Self) "buffer" buffer;
    run_buffer (self : '& Self) :: Run.Trait buffer [] [] [ φ self ] ('& Bytes.t);
  }.

  Class Method_buffer_mut (Self : Set) `{Link Self} : Set := {
    buffer_mut : PolymorphicFunction.t;
    buffer_mut_is_method :: IsTraitMethod.C (trait Self) "buffer_mut" buffer_mut;
    run_buffer_mut (self : '&mut Self) :: Run.Trait buffer_mut [] [] [ φ self ] ('&mut Bytes.t);
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    method_buffer :: Method_buffer Self;
    method_buffer_mut :: Method_buffer_mut Self;
  }.
End ReturnData.
Export (hints) ReturnData.

(*
pub trait LoopControl {
    fn set_instruction_result(&mut self, result: InstructionResult);
    fn set_next_action(&mut self, action: InterpreterAction, result: InstructionResult);
    fn gas(&mut self) -> &mut Gas;
    fn instruction_result(&self) -> InstructionResult;
    fn take_next_action(&mut self) -> InterpreterAction;
}
*)
Module LoopControl.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_interpreter::interpreter_types::LoopControl";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_set_action (Self : Set) `{Link Self} : Set := {
    set_action : PolymorphicFunction.t;
    set_action_is_method :: IsTraitMethod.C (trait Self) "set_action" set_action;
    run_set_action (self : '&mut Self) (action : InterpreterAction.t) ::
      Run.Trait set_action [] [] [ φ self; φ action ] unit;
  }.

  Class Method_set_instruction_result (Self : Set) `{Link Self} : Set := {
    set_instruction_result : PolymorphicFunction.t;
    set_instruction_result_is_method :: IsTraitMethod.C (trait Self) "set_instruction_result" set_instruction_result;
    run_set_instruction_result (self : '&mut Self) (result : InstructionResult.t) ::
      Run.Trait set_instruction_result [] [] [ φ self; φ result ] unit;
  }.

  Class Method_set_next_action (Self : Set) `{Link Self} : Set := {
    set_next_action : PolymorphicFunction.t;
    set_next_action_is_method :: IsTraitMethod.C (trait Self) "set_next_action" set_next_action;
    run_set_next_action (self : '&mut Self) (action : InterpreterAction.t) (result : InstructionResult.t) ::
      Run.Trait set_next_action [] [] [ φ self; φ action; φ result ] unit;
  }.

  Class Method_gas (Self : Set) `{Link Self} : Set := {
    gas : PolymorphicFunction.t;
    gas_is_method :: IsTraitMethod.C (trait Self) "gas" gas;
    run_gas (self : '&mut Self) :: Run.Trait gas [] [] [ φ self ] ('&mut Gas.t);
  }.

  Class Method_instruction_result (Self : Set) `{Link Self} : Set := {
    instruction_result : PolymorphicFunction.t;
    instruction_result_is_method :: IsTraitMethod.C (trait Self) "instruction_result" instruction_result;
    run_instruction_result (self : '& Self) :: Run.Trait instruction_result [] [] [ φ self ] InstructionResult.t;
  }.

  Class Method_take_next_action (Self : Set) `{Link Self} : Set := {
    take_next_action : PolymorphicFunction.t;
    take_next_action_is_method :: IsTraitMethod.C (trait Self) "take_next_action" take_next_action;
    run_take_next_action (self : '&mut Self) :: Run.Trait take_next_action [] [] [ φ self ] InterpreterAction.t;
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    method_set_action :: Method_set_action Self;
    method_set_instruction_result :: Method_set_instruction_result Self;
    method_set_next_action :: Method_set_next_action Self;
    method_gas :: Method_gas Self;
    method_instruction_result :: Method_instruction_result Self;
    method_take_next_action :: Method_take_next_action Self;
  }.
End LoopControl.
Export (hints) LoopControl.

(*
pub trait RuntimeFlag {
    fn is_static(&self) -> bool;
    fn is_eof(&self) -> bool;
    fn is_eof_init(&self) -> bool;
    fn spec_id(&self) -> SpecId;
}
*)
Module RuntimeFlag.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_interpreter::interpreter_types::RuntimeFlag";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_is_static (Self : Set) `{Link Self} : Set := {
    is_static : PolymorphicFunction.t;
    is_static_is_method :: IsTraitMethod.C (trait Self) "is_static" is_static;
    run_is_static (self : '& Self) :: Run.Trait is_static [] [] [ φ self ] bool;
  }.

  Class Method_is_eof (Self : Set) `{Link Self} : Set := {
    is_eof : PolymorphicFunction.t;
    is_eof_is_method :: IsTraitMethod.C (trait Self) "is_eof" is_eof;
    run_is_eof (self : '& Self) :: Run.Trait is_eof [] [] [ φ self ] bool;
  }.

  Class Method_is_eof_init (Self : Set) `{Link Self} : Set := {
    is_eof_init : PolymorphicFunction.t;
    is_eof_init_is_method :: IsTraitMethod.C (trait Self) "is_eof_init" is_eof_init;
    run_is_eof_init (self : '& Self) :: Run.Trait is_eof_init [] [] [ φ self ] bool;
  }.

  Class Method_spec_id (Self : Set) `{Link Self} : Set := {
    spec_id : PolymorphicFunction.t;
    spec_id_is_method :: IsTraitMethod.C (trait Self) "spec_id" spec_id;
    run_spec_id (self : '& Self) :: Run.Trait spec_id [] [] [ φ self ] SpecId.t;
  }.

  Class Run (Self : Set) `{Link Self} : Set := {
    method_is_static :: Method_is_static Self;
    method_is_eof :: Method_is_eof Self;
    method_is_eof_init :: Method_is_eof_init Self;
    method_spec_id :: Method_spec_id Self;
  }.
End RuntimeFlag.
Export (hints) RuntimeFlag.

(*
pub trait InterpreterTypes {
    type Stack: StackTrait;
    type Memory: MemoryTrait;
    type Bytecode: Jumps + Immediates + LegacyBytecode + EofData + EofContainer;
    type ReturnData: ReturnData;
    type Input: InputsTrait;
    type SubRoutineStack: SubRoutineStack;
    type Control: LoopControl;
    type RuntimeFlag: RuntimeFlag;
    type Extend;
}
*)
Module InterpreterTypes.
  Module Types.
    Record t : Type := {
      Stack : Set;
      Memory : Set;
      Memory_Synthetic : Set;
      Memory_Synthetic1 : Set;
      Bytecode : Set;
      ReturnData : Set;
      Input : Set;
      SubRoutineStack : Set;
      Control : Set;
      RuntimeFlag : Set;
      Extend : Set;
    }.

    Class AreLinks (types : t) : Set := {
      H_Stack :: Link types.(Stack);
      H_Memory :: Link types.(Memory);
      H_Memory_Synthetic :: Link types.(Memory_Synthetic);
      H_Memory_Synthetic1 :: Link types.(Memory_Synthetic1);
      H_Bytecode :: Link types.(Bytecode);
      H_ReturnData :: Link types.(ReturnData);
      H_Input :: Link types.(Input);
      H_SubRoutineStack :: Link types.(SubRoutineStack);
      H_Control :: Link types.(Control);
      H_RuntimeFlag :: Link types.(RuntimeFlag);
      H_Extend :: Link types.(Extend);
    }.
  End Types.
  Export (hints) Types.

  Class Run
      (Self : Set) `{Link Self}
      (types : Types.t) `{Types.AreLinks types} :
      Set := {
    Stack_IsAssociated :
      IsTraitAssociatedType
        "revm_interpreter::interpreter_types::InterpreterTypes" [] [] (Φ Self)
        "Stack" (Φ types.(Types.Stack));
    run_StackTrait_for_Stack :: StackTrait.Run types.(Types.Stack);
    Memory_IsAssociated :
      IsTraitAssociatedType
        "revm_interpreter::interpreter_types::InterpreterTypes" [] [] (Φ Self)
        "Memory" (Φ types.(Types.Memory));
    run_MemoryTrait_for_Memory ::
      MemoryTrait.Run
        types.(Types.Memory)
        types.(Types.Memory_Synthetic)
        types.(Types.Memory_Synthetic1);
    Bytecode_IsAssociated :
      IsTraitAssociatedType
        "revm_interpreter::interpreter_types::InterpreterTypes" [] [] (Φ Self)
        "Bytecode" (Φ types.(Types.Bytecode));
    run_Jumps_for_Bytecode :: Jumps.Run types.(Types.Bytecode);
    run_Immediates_for_Bytecode :: Immediates.Run types.(Types.Bytecode);
    run_LoopControl_for_Bytecode :: LoopControl.Run types.(Types.Bytecode);
    run_LegacyBytecode_for_Bytecode :: LegacyBytecode.Run types.(Types.Bytecode);
    run_EofData_for_Bytecode :: EofData.Run types.(Types.Bytecode);
    run_EofContainer_for_Bytecode :: EofContainer.Run types.(Types.Bytecode);
    ReturnData_IsAssociated :
      IsTraitAssociatedType
        "revm_interpreter::interpreter_types::InterpreterTypes" [] [] (Φ Self)
        "ReturnData" (Φ types.(Types.ReturnData));
    run_ReturnData_for_ReturnData :: ReturnData.Run types.(Types.ReturnData);
    Input_IsAssociated :
      IsTraitAssociatedType
        "revm_interpreter::interpreter_types::InterpreterTypes" [] [] (Φ Self)
        "Input" (Φ types.(Types.Input));
    run_InputsTrait_for_Input :: InputsTrait.Run types.(Types.Input);
    SubRoutineStack_IsAssociated :
      IsTraitAssociatedType
        "revm_interpreter::interpreter_types::InterpreterTypes" [] [] (Φ Self)
        "SubRoutineStack" (Φ types.(Types.SubRoutineStack));
    run_SubRoutineStack_for_SubRoutineStack :: SubRoutineStack.Run types.(Types.SubRoutineStack);
    Control_IsAssociated :
      IsTraitAssociatedType
        "revm_interpreter::interpreter_types::InterpreterTypes" [] [] (Φ Self)
        "Control" (Φ types.(Types.Control));
    run_LoopControl_for_Control :: LoopControl.Run types.(Types.Control);
    RuntimeFlag_IsAssociated :
      IsTraitAssociatedType
        "revm_interpreter::interpreter_types::InterpreterTypes" [] [] (Φ Self)
        "RuntimeFlag" (Φ types.(Types.RuntimeFlag));
    run_RuntimeFlag_for_RuntimeFlag :: RuntimeFlag.Run types.(Types.RuntimeFlag);
  }.
End InterpreterTypes.
Export (hints) InterpreterTypes.
