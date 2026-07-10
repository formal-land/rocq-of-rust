Require Import links.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed_FixedBytes.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.convert.links.mod.
Require Import core.links.cmp.
Require Import core.links.option.
Require Import core.num.links.mod.
Require Import core.ops.links.range.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_interpreter.gas.links.calc.
Require Import revm.revm_interpreter.instructions.contract.call_helpers.
Require Import revm.revm_interpreter.interpreter.links.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.

#[export] Existing Instance Option.IsLink.
#[export] Existing Instance FixedBytes.IsLink.

Module LoadAccAndCalcGasResult.
  Record t : Set := {
    gas_limit : u64;
    bytecode : Bytecode.t;
    bytecode_hash : aliases.B256.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.tuple [
      Φ u64;
      Φ Bytecode.t;
      Φ aliases.B256.t
    ];
    φ x := Value.Tuple [
      φ x.(gas_limit);
      φ x.(bytecode);
      φ x.(bytecode_hash)
    ];
  }.

  Definition of_ty :
    OfTy.t (Ty.tuple [
      Φ u64;
      Φ Bytecode.t;
      Φ aliases.B256.t
    ]).
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Module SubPointer.
    Definition get_gas_limit : SubPointer.Runner.t t (Pointer.Index.Tuple 0) :=
    {|
      SubPointer.Runner.projection x := Some x.(gas_limit);
      SubPointer.Runner.injection x y := Some (x <| gas_limit := y |>);
    |}.

    Lemma get_gas_limit_is_valid :
      SubPointer.Runner.Valid.t get_gas_limit.
    Proof. now constructor. Qed.
    Smpl Add apply get_gas_limit_is_valid : run_sub_pointer.

    Definition get_bytecode : SubPointer.Runner.t t (Pointer.Index.Tuple 1) :=
    {|
      SubPointer.Runner.projection x := Some x.(bytecode);
      SubPointer.Runner.injection x y := Some (x <| bytecode := y |>);
    |}.

    Lemma get_bytecode_is_valid :
      SubPointer.Runner.Valid.t get_bytecode.
    Proof. now constructor. Qed.
    Smpl Add apply get_bytecode_is_valid : run_sub_pointer.

    Definition get_bytecode_hash : SubPointer.Runner.t t (Pointer.Index.Tuple 2) :=
    {|
      SubPointer.Runner.projection x := Some x.(bytecode_hash);
      SubPointer.Runner.injection x y := Some (x <| bytecode_hash := y |>);
    |}.

    Lemma get_bytecode_hash_is_valid :
      SubPointer.Runner.Valid.t get_bytecode_hash.
    Proof. now constructor. Qed.
    Smpl Add apply get_bytecode_hash_is_valid : run_sub_pointer.
  End SubPointer.
End LoadAccAndCalcGasResult.

(*
pub fn resize_memory(
    interpreter: &mut Interpreter<impl InterpreterTypes>,
    offset: U256,
    len: U256,
) -> Option<Range<usize>>
*)
Instance run_resize_memory
  {WIRE : Set} `{Link WIRE}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
  (offset len : aliases.U256.t) :
  Run.Trait
    instructions.contract.call_helpers.resize_memory
    [] [Φ WIRE] [φ interpreter; φ offset; φ len]
    (option (Range.t usize)).
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_LoopControl_for_Control.
  destruct run_MemoryTrait_for_Memory.
  run_symbolic.
  all: first [
    eapply (@interpreter.links.shared_memory.run_resize_memory
      WIRE_types.(InterpreterTypes.Types.Memory)
      WIRE_types.(InterpreterTypes.Types.Memory_Synthetic)
      WIRE_types.(InterpreterTypes.Types.Memory_Synthetic1)
      H0.(InterpreterTypes.Types.H_Memory)
      H0.(InterpreterTypes.Types.H_Memory_Synthetic)
      H0.(InterpreterTypes.Types.H_Memory_Synthetic1)
      (run_InterpreterTypes_for_WIRE.(InterpreterTypes.run_MemoryTrait_for_Memory)))
  ].
Defined.
Global Opaque run_resize_memory.

(*
pub fn get_memory_input_and_out_ranges(
    interpreter: &mut Interpreter<impl InterpreterTypes>,
) -> Option<(Range<usize>, Range<usize>)>
*)
Instance run_get_memory_input_and_out_ranges
  {WIRE : Set} `{Link WIRE}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : '&mut (Interpreter.t WIRE WIRE_types)) :
  Run.Trait
    instructions.contract.call_helpers.get_memory_input_and_out_ranges
    [] [Φ WIRE] [φ interpreter]
    (option (Range.t usize * Range.t usize)).
Proof.
  constructor.
  destruct (Impl_Try_for_Option.run (Range.t usize)).
  destruct (Impl_FromResidual_Infallible_for_Option.run (Range.t usize * Range.t usize)).
  destruct (Impl_AsRef_for_Slice.run u8).
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_MemoryTrait_for_Memory.
  destruct run_Deref_for_Synthetic.
  run_symbolic.
  all: first [
    eapply Impl_usize.run_saturating_add
  ].
Defined.
Global Opaque run_get_memory_input_and_out_ranges.

(*
pub fn load_acc_and_calc_gas<H: Host + ?Sized>(
    context: &mut InstructionContext<'_, H, impl InterpreterTypes>,
    to: Address,
    transfers_value: bool,
    create_empty_account: bool,
    stack_gas_limit: u64,
) -> Option<(u64, Bytecode, B256)>
*)
Instance run_load_acc_and_calc_gas
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (context : '&mut (InstructionContext.t H WIRE WIRE_types))
  (to : Address.t)
  (transfers_value create_empty_account : bool)
  (stack_gas_limit : u64) :
  Run.Trait
    instructions.contract.call_helpers.load_acc_and_calc_gas
    [] [Φ H; Φ WIRE]
    [φ context; φ to; φ transfers_value; φ create_empty_account; φ stack_gas_limit]
    (option LoadAccAndCalcGasResult.t).
Proof.
Admitted.
Global Opaque run_load_acc_and_calc_gas.
