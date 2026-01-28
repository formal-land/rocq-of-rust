Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.links.cmp.
Require Import core.num.simulate.mod.
Require Import core.simulate.cmp.
Require Import core.simulate.result.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.bitwise.byte.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.links.lib.
Require Import ruint.simulate.bits.
Require Import ruint.simulate.cmp.
Require Import ruint.simulate.from.
Require Import ruint.simulate.lib.

Definition op_byte
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  popn_top_macro interpreter {| Integer.value := 1 |} id (fun arr top interpreter =>
    let '{| ArrayPair.x := op1 |} := arr.(array.value) in
    let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
    let o1 := as_usize_saturated_macro op1 in
    let result :=
      if o1.(Integer.value) <? 32
      then
        (* `31 - o1` because `byte` returns LE, while we want BE *)
        {| Uint.value := (Impl_Uint.byte op2 {| Integer.value := 31 - o1.(Integer.value) |}).(Integer.value) |}
      else
        {| Uint.value := 0 |} in
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack) result in
    interpreter
      <| Interpreter.stack := stack |>
  )).

Lemma op_byte_eq
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
      (run_byte run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        op_byte interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
Opaque Z.sub.
  intros.
  unfold op_byte.
  gas_macro_eq InterpreterTypesEq.
  popn_top_macro_eq InterpreterTypesEq.
  cbn.
  match goal with
  | array : array.t aliases.U256.t _ |- _ => destruct array as [[op1 []]]; cbn
  end.
  eapply Run.Let with (result := (Output.Success (as_usize_saturated_macro op1), _)). {
    eapply Run.Call. {
      apply Impl_Uint.as_limbs_eq; repeat unshelve econstructor.
    }
    repeat (cbn || apply Run.Pure || eapply Run.Call).
    assert (H_compares :
        (((op1.(Uint.value) / 2^64) mod 2^64 =? 0) &&
    ((op1.(Uint.value) / 2^128) mod 2^64 =?
      0) &&
    (op1.(Uint.value) / 2^192 =? 0)) = true ->
      op1.(Uint.value) <= 2 ^ 64 - 1
    ) by lia.
    unfold Bool.eqb.
    destruct (_ && _) eqn:H_and_eq; cbn.
    { eapply Run.Call. {
        apply Run.Pure.
      }
      cbn.
      eapply Run.Call. {
        apply Impl_usize.max_eq.
      }
      cbn.
      eapply Run.Call. {
        apply Impl_Result_T_E.unwrap_or_eq.
      }
      cbn.
      apply Run.PureEq; repeat f_equal.
      destruct op1 as [op1]; cbn in *.
      replace (as_usize_saturated_macro _) with (op1 : usize). 2: {
        unfold as_usize_saturated_macro; cbn.
        now rewrite Z.min_l by lia.
      }
      unfold M.cast_integer; cbn.
      f_equal; [hauto lq: on|].
      lia.
    }
    { eapply Run.Call. {
        apply Impl_u64.max_eq.
      }
      cbn.
      eapply Run.Call. {
        cbn.
        apply Run.Pure.
      }
      eapply Run.Call. {
        apply Impl_usize.max_eq.
      }
      cbn.
      eapply Run.Call. {
        apply Impl_Result_T_E.unwrap_or_eq.
      }
      cbn.
      apply Run.PureEq; repeat f_equal.
      unfold M.cast_integer, as_usize_saturated_macro; cbn.
      f_equal; [hauto lq: on|].
      destruct op1 as [op1]; cbn in *.
      rewrite Z.min_r; [reflexivity|].
      assert (0 <= op1) by admit.
      lia.
    }
  }
  cbn.
  apply Run.LetUnfold.
  get_can_access.
  eapply Run.Call. {
    apply Run.Pure.
  }
  cbn.
  eapply Run.Call. {
    apply Run.Pure.
  }
  cbn.
  destruct (_ <? 32) eqn:H_lt_eq; cbn.
  { get_can_access.
    eapply Run.Call. {
      apply Run.Pure.
    }
    cbn.
    eapply Run.Call. {
      apply Impl_Uint.byte_eq; repeat unshelve econstructor.
    }
    cbn.
    eapply Run.Call. {
      apply Impl_Uint.from_eq.
      { typeclasses eauto. }
      { easy. }
    }
    cbn.
    get_can_access.
    destruct op1 as [op1]; cbn in *.
    assert (0 <= op1) by admit.
    replace (_ mod (2 ^ 64)) with (31 - Z.min op1 (2^64 - 1)) by lia.
    apply Run.Pure.
  }
  { eapply Run.Call. {
      apply Impl_Uint.ZERO_eq.
    }
    cbn.
    get_can_access.
    apply Run.PureEq; repeat f_equal.
  }
  (* Make sure there are no goals left *)
  Unshelve.
  all: easy.
Transparent Z.sub.
Admitted.
