Require Import links.RocqOfRust.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.convert.links.mod.
Require Import core.links.cmp.
Require Import core.links.option.
Require Import core.num.links.mod.
Require Import core.ops.links.range.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_interpreter.gas.links.calc.
Require Import revm.revm_interpreter.instructions.contract.call_helpers.
Require Import revm.revm_interpreter.interpreter.links.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.

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
  run_symbolic.
Defined.
Global Opaque run_resize_memory.

(*
pub fn get_memory_input_and_out_ranges(
    interpreter: &mut Interpreter<impl InterpreterTypes>,
) -> Option<(Bytes, Range<usize>)>
*)
Instance run_get_memory_input_and_out_ranges
  {WIRE : Set} `{Link WIRE}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : '&mut (Interpreter.t WIRE WIRE_types)) :
  Run.Trait
    instructions.contract.call_helpers.get_memory_input_and_out_ranges
    [] [Φ WIRE] [φ interpreter]
    (option (Bytes.t * Range.t usize)).
Proof.
  constructor.
  destruct (Impl_Try_for_Option.run (Range.t usize)).
  destruct (Impl_FromResidual_Infallible_for_Option.run (Bytes.t * Range.t usize)).
  destruct (Impl_AsRef_for_Slice.run u8).
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_MemoryTrait_for_Memory.
  destruct run_Deref_for_Synthetic.
  run_symbolic.
Defined.
Global Opaque run_get_memory_input_and_out_ranges.

(*
pub fn calc_call_gas(
    interpreter: &mut Interpreter<impl InterpreterTypes>,
    account_load: AccountLoad,
    has_transfer: bool,
    local_gas_limit: u64,
) -> Option<u64>
*)
Instance run_calc_call_gas
  {WIRE : Set} `{Link WIRE}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
  (account_load : AccountLoad.t)
  (has_transfer : bool)
  (local_gas_limit : u64) :
  Run.Trait
    instructions.contract.call_helpers.calc_call_gas
    [] [Φ WIRE] [φ interpreter; φ account_load; φ has_transfer; φ local_gas_limit]
    (option u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_calc_call_gas.
