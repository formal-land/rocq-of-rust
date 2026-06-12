Require Import links.RocqOfRust.
Require Import alloy_primitives.bits.links.fixed.
Require Import core.array.links.mod.
Require Import core.convert.links.num.
Require Import core.convert.links.mod.
Require Import core.ops.links.range.
Require Import core.links.array.
Require Import core.links.result.
Require Import core.num.links.mod.
Require Import core.slice.links.index.
Require Import core.slice.links.mod.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.links.calc.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.interpreter.links.shared_memory.
Require Import ruint.links.bytes.
Require Import ruint.links.from.
Require Import ruint.links.lib.

Definition data_instruction
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

(*
pub fn data_load<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_data_load
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
  (_host : '&mut H) :
  Run.Trait
    (data_instruction interpreter _host) [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  cbn.
  eapply Run.PureSuccess with (value := tt).
  reflexivity.
Defined.
Global Opaque run_data_load.

(*
pub fn data_loadn<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_data_loadn
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
  (_host : '&mut H) :
  Run.Trait
    (data_instruction interpreter _host) [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  cbn.
  eapply Run.PureSuccess with (value := tt).
  reflexivity.
Defined.
Global Opaque run_data_loadn.

(*
pub fn data_size<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_data_size
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
  (_host : '&mut H) :
  Run.Trait
    (data_instruction interpreter _host) [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  cbn.
  eapply Run.PureSuccess with (value := tt).
  reflexivity.
Defined.
Global Opaque run_data_size.

(*
pub fn data_copy<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_data_copy
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
  (_host : '&mut H) :
  Run.Trait
    (data_instruction interpreter _host) [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  cbn.
  eapply Run.PureSuccess with (value := tt).
  reflexivity.
Defined.
Global Opaque run_data_copy.
