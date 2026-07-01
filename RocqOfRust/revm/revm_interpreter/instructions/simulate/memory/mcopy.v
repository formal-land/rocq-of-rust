Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.num.simulate.mod.
Require Import core.ops.simulate.deref.
Require Import core.simulate.cmp.
Require Import core.simulate.option.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.memory.mcopy.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.interpreter.simulate.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.bytes.
Require Import ruint.simulate.from.
Require Import ruint.simulate.lib.

Definition mcopy
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{IInterpreterTypes : !InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  check_macro interpreter SpecId.CANCUN id (fun interpreter =>
  popn_macro interpreter {| Integer.value := 3 |} id (fun arr interpreter =>
  let '⟬ dst; src; len ⟭ := arr.(array.value) in
  as_usize_or_fail_ret_macro interpreter len None id (fun len interpreter =>
  gas_or_fail_macro interpreter (calc.copy_cost_verylow len) id (fun interpreter =>
  if i[len] =? 0 then
    interpreter
  else
    as_usize_or_fail_ret_macro interpreter dst None id (fun dst interpreter =>
    as_usize_or_fail_ret_macro interpreter src None id (fun src interpreter =>
    let max_offset : usize := {| Integer.value := Z.max i[dst] i[src] |} in
    resize_memory_macro interpreter max_offset len id (fun interpreter =>
    let memory :=
      IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.copy)
        interpreter.(Interpreter.memory) dst src len in
    interpreter <| Interpreter.memory := memory |>
  ))))))).

Lemma mcopy_eq
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
  let context := {|
    instruction_context.InstructionContext.interpreter := ref_interpreter;
    instruction_context.InstructionContext.host := ref_host;
  |} in
  {{
    SimulateM.eval_f
      (run_mcopy run_InterpreterTypes_for_WIRE context)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        mcopy interpreter;
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  with_strategy transparent [run_mcopy] unfold mcopy, run_mcopy; cbn.
  unfold check_macro; cbn.
  apply Run.LetUnfold.
  eapply Run.Call; [
    apply InterpreterTypesEq
      .(InterpreterTypes.Eq.RuntimeFlag_for_RuntimeFlag)
      .(RuntimeFlag.Eq.spec_id)
  |].
  cbn.
  eapply Run.Call; [
    apply Impl_SpecId.is_enabled_in_eq
  |].
  cbn.
  eapply Run.Call; [
    apply Run.Pure
  |].
  cbn.
  eapply Run.Call; [
    apply Run.Pure
  |].
  cbn.
  destruct Impl_SpecId.is_enabled_in; cbn. 2: {
    s. {
      eapply halt_not_activated_eq;
        try exact InterpreterTypesEq.
    }
    repeat s.
  }
  popn_macro_eq InterpreterTypesEq.
  match goal with
  | array : array.t aliases.U256.t _ |- _ =>
    destruct array as [[dst [src [len []]]]]
  end.
  as_usize_or_fail_ret_macro_eq InterpreterTypesEq.
  s. {
    apply calc.copy_cost_verylow_eq.
  }
  unfold gas_or_fail_macro, calc.copy_cost_verylow.
  gas_macro_eq idtac.
  destruct (_ =? 0) eqn:?.
  - repeat s.
    try rewrite Heqb; cbn.
    repeat s.
  - repeat s.
    try rewrite Heqb; cbn.
    repeat s.
    {
      s_apply Impl_Uint.as_limbs_eq.
    }
    s. {
      apply Impl_usize.max_eq.
    }
    s.
    destruct (_ || _) eqn:?; cbn.
    + s. {
        eapply halt_eq;
          try exact InterpreterTypesEq.
      }
      repeat s.
    + repeat s.
      {
        s_apply Impl_Uint.as_limbs_eq.
      }
      s. {
        apply Impl_usize.max_eq.
      }
      s.
      destruct (_ || _) eqn:?; cbn.
      * discriminate.
      * change ((2 ^ 64 - 1) mod 2 ^ 64) with (2 ^ 64 - 1).
        repeat match goal with
        | H : ?e = false |- context[?e] => rewrite H
        end; cbn.
        destruct (
          (src.(Uint.value) mod 2 ^ 64 >? 2 ^ 64 - 1)
          || negb ((src.(Uint.value) / 2 ^ 64) mod 2 ^ 64 =? 0)
          || negb ((src.(Uint.value) / 2 ^ 128) mod 2 ^ 64 =? 0)
          || negb ((src.(Uint.value) / 2 ^ 192) mod 2 ^ 64 =? 0)
        ) eqn:?; cbn.
        { s. {
            eapply halt_eq;
              try exact InterpreterTypesEq.
          }
          repeat s.
        }
        { s. {
            apply Impl_Ord_for_usize.toplevel_max_eq.
          }
          resize_memory_macro_eq InterpreterTypesEq.
          - step; cbn.
            + change
                {| Integer.value :=
                  Z.max ((dst.(Uint.value) mod 2 ^ 64) mod 2 ^ 64)
                    ((src.(Uint.value) mod 2 ^ 64) mod 2 ^ 64)
                |}
                with
                (Z.max ((dst.(Uint.value) mod 2 ^ 64) mod 2 ^ 64)
                  ((src.(Uint.value) mod 2 ^ 64) mod 2 ^ 64) : usize)
                in Heqp.
              rewrite Heqp in Heqb3.
              cbn in Heqb3.
              discriminate.
            + change
                {| Integer.value :=
                  Z.max ((dst.(Uint.value) mod 2 ^ 64) mod 2 ^ 64)
                    ((src.(Uint.value) mod 2 ^ 64) mod 2 ^ 64)
                |}
                with
                (Z.max ((dst.(Uint.value) mod 2 ^ 64) mod 2 ^ 64)
                  ((src.(Uint.value) mod 2 ^ 64) mod 2 ^ 64) : usize)
                in Heqp.
              rewrite Heqp; cbn.
              s. {
                apply InterpreterTypesEq.
              }
              s.
          - change
              {| Integer.value :=
                Z.max ((dst.(Uint.value) mod 2 ^ 64) mod 2 ^ 64)
                  ((src.(Uint.value) mod 2 ^ 64) mod 2 ^ 64)
              |}
              with
              (Z.max ((dst.(Uint.value) mod 2 ^ 64) mod 2 ^ 64)
                ((src.(Uint.value) mod 2 ^ 64) mod 2 ^ 64) : usize)
              in Heqp.
            rewrite Heqp; cbn.
            s. {
              eapply halt_memory_oog_eq;
                try exact InterpreterTypesEq.
            }
            repeat s.
        }
Qed.
