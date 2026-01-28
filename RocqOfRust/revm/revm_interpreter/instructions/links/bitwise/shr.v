Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.convert.links.num.
Require Import core.links.cmp.
Require Import core.links.result.
Require Import core.num.links.error.
Require Import core.num.links.mod.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.instructions.bitwise.
Require Import revm.revm_specification.links.hardfork.
Require Import ruint.links.bits.
Require Import ruint.links.cmp.
Require Import ruint.links.from.
Require Import ruint.links.lib.

Instance run_bitwise_shr
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
    (_host : '&mut H) :
  Run.Trait
    instructions.bitwise.shr [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct Impl_TryFrom_u64_for_usize.run.
  destruct (Impl_Shr_for_Uint.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  run_symbolic.
Defined.
Global Opaque run_bitwise_shr.
