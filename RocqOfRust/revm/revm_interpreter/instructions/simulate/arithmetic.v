Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.arithmetic.
Require Import revm.revm_interpreter.instructions.simulate.i256.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_specification.simulate.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.add.
Require Import ruint.simulate.bits.
Require Import ruint.simulate.cmp.
Require Import ruint.simulate.div.
Require Import ruint.simulate.from.
Require Import ruint.simulate.lib.
Require Import ruint.simulate.modular.
Require Import ruint.simulate.mul.
Require Import ruint.simulate.pow.

Definition add
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  popn_top_macro interpreter 1 id (fun arr top interpreter =>
  let '⟬ op1 ⟭ := arr.(array.value) in
  let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
  let stack :=
    top.(RefStub.injection)
      interpreter.(Interpreter.stack) (Impl_Uint.wrapping_add op1 op2) in
  interpreter
    <| Interpreter.stack := stack |>
  )).

Lemma add_eq
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
      (run_add run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        add interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  unfold add.
  gas_macro_eq InterpreterTypesEq.
  popn_top_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t aliases.U256.t _ |- _ =>
    destruct array as [[op1 []]]
  end.
  s. {
    apply Impl_Uint.wrapping_add_eq.
  } 
  s.
Qed.

Definition mul
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.LOW id (fun interpreter =>
  popn_top_macro interpreter 1 id (fun arr top interpreter =>
  let '⟬ op1 ⟭ := arr.(array.value) in
  let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
  let stack :=
    top.(RefStub.injection)
      interpreter.(Interpreter.stack) (Impl_Uint.wrapping_mul op1 op2) in
  interpreter
    <| Interpreter.stack := stack |>
  )).

Lemma mul_eq
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
      (run_mul run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        mul interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  unfold mul.
  gas_macro_eq InterpreterTypesEq.
  popn_top_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t aliases.U256.t _ |- _ =>
    destruct array as [[op1 []]]
  end.
  s. {
    apply Impl_Uint.wrapping_mul_eq.
  }
  s.
Qed.

Definition sub
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  popn_top_macro interpreter 1 id (fun arr top interpreter =>
  let '⟬ op1 ⟭ := arr.(array.value) in
  let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
  let stack :=
    top.(RefStub.injection)
      interpreter.(Interpreter.stack) (Impl_Uint.wrapping_sub op1 op2) in
  interpreter
    <| Interpreter.stack := stack |>
  )).

Lemma sub_eq
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
      (run_sub run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        sub interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  unfold sub.
  gas_macro_eq InterpreterTypesEq.
  popn_top_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t aliases.U256.t _ |- _ =>
    destruct array as [[op1 []]]
  end.
  s. {
    apply Impl_Uint.wrapping_sub_eq.
  }
  s.
Qed.

Definition div
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.LOW id (fun interpreter =>
  popn_top_macro interpreter 1 id (fun arr top interpreter =>
  let '⟬ op1 ⟭ := arr.(array.value) in
  let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
  if Impl_Uint.is_zero op2 then
    interpreter
  else
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack)
        (Impl_Uint.wrapping_div op1 op2) in
    interpreter
      <| Interpreter.stack := stack |>
  )).

Lemma div_eq
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
      (run_div run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        div interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  unfold div.
  gas_macro_eq InterpreterTypesEq.
  popn_top_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t aliases.U256.t _ |- _ =>
    destruct array as [[op1 []]]
  end.
  s. {
    s_apply @Impl_Uint.is_zero_eq.
  }
  destruct Impl_Uint.is_zero; [s|].
  s. {
    apply Impl_Uint.wrapping_div_eq.
  }
  s.
Qed.

Definition sdiv
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.LOW id (fun interpreter =>
  popn_top_macro interpreter 1 id (fun arr top interpreter =>
  let '⟬ op1 ⟭ := arr.(array.value) in
  let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
  let stack :=
    top.(RefStub.injection)
      interpreter.(Interpreter.stack) (i256_div op1 op2) in
  interpreter
    <| Interpreter.stack := stack |>
  )).

Lemma sdiv_eq
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
      (run_sdiv run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        sdiv interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  unfold sdiv.
  gas_macro_eq InterpreterTypesEq.
  popn_top_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t aliases.U256.t _ |- _ =>
    destruct array as [[op1 []]]
  end.
  s. {
    apply i256_div_eq.
  }
  s.
Qed.

Definition rem
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.LOW id (fun interpreter =>
  popn_top_macro interpreter 1 id (fun arr top interpreter =>
  let '⟬ op1 ⟭ := arr.(array.value) in
  let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
  if Impl_Uint.is_zero op2 then
    interpreter
  else
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack)
        (Impl_Uint.wrapping_rem op1 op2) in
    interpreter
      <| Interpreter.stack := stack |>
  )).

Lemma rem_eq
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
      (run_rem run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        rem interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  unfold rem.
  gas_macro_eq InterpreterTypesEq.
  popn_top_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t aliases.U256.t _ |- _ =>
    destruct array as [[op1 []]]
  end.
  s. {
    s_apply @Impl_Uint.is_zero_eq.
  }
  destruct Impl_Uint.is_zero; [s|].
  s. {
    apply Impl_Uint.wrapping_rem_eq.
  }
  s.
Qed.

Definition smod
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.LOW id (fun interpreter =>
  popn_top_macro interpreter 1 id (fun arr top interpreter =>
  let '⟬ op1 ⟭ := arr.(array.value) in
  let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
  let stack :=
    top.(RefStub.injection)
      interpreter.(Interpreter.stack) (i256_mod op1 op2) in
  interpreter
    <| Interpreter.stack := stack |>
  )).

Lemma smod_eq
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
      (run_smod run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        smod interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  unfold smod.
  gas_macro_eq InterpreterTypesEq.
  popn_top_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t aliases.U256.t _ |- _ =>
    destruct array as [[op1 []]]
  end.
  s. {
    apply i256_mod_eq.
  }
  s.
Qed.

Definition addmod
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.MID id (fun interpreter =>
  popn_top_macro interpreter 2 id (fun arr top interpreter =>
  let '⟬ op1; op2 ⟭ := arr.(array.value) in
  let op3 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
  let stack :=
    top.(RefStub.injection)
      interpreter.(Interpreter.stack) (Impl_Uint.add_mod op1 op2 op3) in
  interpreter
    <| Interpreter.stack := stack |>
  )).

Lemma addmod_eq
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
      (run_addmod run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        addmod interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  unfold addmod.
  gas_macro_eq InterpreterTypesEq.
  popn_top_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t aliases.U256.t _ |- _ =>
    destruct array as [[op1 [op2 []]]]
  end.
  s. {
    apply Impl_Uint.add_mod_eq.
  }
  s.
Qed.

Definition mulmod
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.MID id (fun interpreter =>
  popn_top_macro interpreter 2 id (fun arr top interpreter =>
  let '⟬ op1; op2 ⟭ := arr.(array.value) in
  let op3 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
  let stack :=
    top.(RefStub.injection)
      interpreter.(Interpreter.stack) (Impl_Uint.mul_mod op1 op2 op3) in
  interpreter
    <| Interpreter.stack := stack |>
  )).

Lemma mulmod_eq
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
      (run_mulmod run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        mulmod interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  unfold mulmod.
  gas_macro_eq InterpreterTypesEq.
  popn_top_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t aliases.U256.t _ |- _ =>
    destruct array as [[op1 [op2 []]]]
  end.
  s. {
    apply Impl_Uint.mul_mod_eq.
  }
  s.
Qed.

Definition exp
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  let spec_id :=
    IInterpreterTypes
        .(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
        .(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  popn_top_macro interpreter 1 id (fun arr top interpreter =>
  let '⟬ op1 ⟭ := arr.(array.value) in
  let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
  gas_or_fail_macro interpreter (exp_cost spec_id op2) id (fun interpreter =>
  let stack :=
    top.(RefStub.injection)
      interpreter.(Interpreter.stack) (Impl_Uint.pow op1 op2) in
  interpreter
    <| Interpreter.stack := stack |>
  )).

Lemma exp_eq
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
      (run_exp run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        exp IInterpreterTypes interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  unfold exp.
  s. {
    apply InterpreterTypesEq.
  }
  popn_top_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t aliases.U256.t _ |- _ =>
    destruct array as [[op1 []]]
  end.
  s. {
    apply exp_cost_eq.
  }
  unfold gas_macro.
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply Impl_Gas.record_cost_eq.
  }
  destruct Impl_Gas.record_cost.
  { s. {
      apply Impl_Uint.pow_eq.
    }
    s.
  }
  { s. {
      apply InterpreterTypesEq.
    }
    s.
  }
Qed.

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
    let ext_limb0 := ext.(Uint.value) mod 2^64 in
    let bit_index : usize := {| Integer.value := 8 * ext_limb0 + 7 |} in
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
    Show.
    apply Impl_Sub_for_Uint.Eq.I.
  }
  s. {
    s_apply @Impl_Uint.from_eq.
  }
  s. {
    s_apply @Impl_Uint.from_eq.
  }
Qed.
