Require Import links.RocqOfRust.
Require Import alloc.links.alloc.
Require Import alloc.links.slice.
Require Import alloc.vec.links.mod.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.convert.links.mod.
Require Import core.convert.links.num.
Require Import core.fmt.links.mod.
Require Import core.links.option.
Require Import core.links.panicking.
Require Import core.links.result.
Require Import core.num.links.mod.
Require Import revm.revm_bytecode.eof.links.types_section.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.instructions.control.
Require Import revm.revm_interpreter.interpreter.links.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import ruint.links.cmp.
Require Import ruint.links.from.
Require Import ruint.links.lib.

(*
pub fn jumpdest_or_nop<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Definition jumpdest_or_nop
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
    (_host : '&mut H) :
    PolymorphicFunction.t :=
  fun _ _ args =>
    match args with
    | [_; _] => LowM.Pure (inl (φ tt))
    | _ => M.impossible "wrong number of arguments"
    end.

Instance run_jumpdest_or_nop
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
    (_host : '&mut H) :
  Run.Trait
    (jumpdest_or_nop interpreter _host) [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  cbn.
  eapply Run.PureSuccess with (value := tt).
  reflexivity.
Defined.
Global Opaque run_jumpdest_or_nop.
