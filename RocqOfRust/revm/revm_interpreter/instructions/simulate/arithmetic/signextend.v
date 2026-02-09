Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.arithmetic.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.links.lib.
Require Import ruint.simulate.add.
Require Import ruint.simulate.bits.
Require Import ruint.simulate.cmp.
Require Import ruint.simulate.from.
Require Import ruint.simulate.lib.

Definition signextend
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.LOW id (fun interpreter =>
  popn_top_macro interpreter 1 id (fun arr top interpreter =>
  let '⟬ ext ⟭ := arr.(array.value) in
  let x := top.(RefStub.projection) interpreter.(Interpreter.stack) in
  if Impl_PartialOrd_for_Uint.lt ext {| Uint.value := 31 |} then
    let ext_limb0 : u64 := ext.(Uint.value) mod 2^64 in
    let bit_index := M.cast_integer IntegerKind.Usize (8 *i ext_limb0 +i 7) in
    let bit := Impl_Uint.bit x bit_index in
    let mask :=
      Impl_Uint.wrapping_sub
        (Impl_Shl_for_Uint.shl {| Uint.value := 1 |} bit_index)
        {| Uint.value := 1 |} in
    let result :=
      if bit then
        Impl_BitOr_for_Uint.bitor x (Impl_Not_for_Uint.not mask)
      else
        Impl_BitAnd_for_Uint.bitand x mask in
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack) result in
    interpreter
      <| Interpreter.stack := stack |>
  else
    interpreter
  )).

Lemma signextend_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_host : '&mut H := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_signextend run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        signextend interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  unfold signextend.
  gas_macro_eq InterpreterTypesEq.
  popn_top_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t aliases.U256.t _ |- _ =>
    destruct array as [[ext []]]
  end.
  s. {
    s_apply @Impl_Uint.from_eq.
  }
  s. {
    s_apply @Impl_PartialOrd_for_Uint.Eq.I.
  }
  s.
  destruct Impl_PartialOrd_for_Uint.lt; [|s].
  s. {
    s_apply Impl_Uint.as_limbs_eq.
  }
  s. {
    s_apply Impl_Uint.bit_eq.
  }
  s. {
    s_apply @Impl_Uint.from_eq.
  }
  s. {
    apply Impl_Shl_for_Uint.Eq.I.
  }
  s. {
    s_apply @Impl_Uint.from_eq.
  }
  s. {
    apply Impl_Sub_for_Uint.Eq.I.
  }
  s.
  destruct Impl_Uint.bit.
  { s. {
      apply Impl_Not_for_Uint.Eq.I.
    }
    s. {
      apply Impl_BitOr_for_Uint.Eq.I.
    }
    s.
  }
  { s. {
      apply Impl_BitAnd_for_Uint.Eq.I.
    }
    s.
  }
Qed.
