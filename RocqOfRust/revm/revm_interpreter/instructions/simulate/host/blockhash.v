Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.num.simulate.mod.
Require Import core.simulate.option.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.host.blockhash.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.instructions.simulate.utility.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.links.lib.
Require Import ruint.simulate.add.
Require Import ruint.simulate.bytes.
Require Import ruint.simulate.lib.

Definition blockhash
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  popn_top_macro interpreter 0
    (fun interpreter => (interpreter, host)) (fun _ number_stub interpreter =>

  let requested_number := number_stub.(RefStub.projection) interpreter.(Interpreter.stack) in
  let block_number := IHost.(Host.block_number) host in
  match Impl_Uint.checked_sub block_number requested_number with
  | None =>
    let stack :=
      number_stub.(RefStub.injection) interpreter.(Interpreter.stack) Impl_Uint.ZERO in
    (interpreter <| Interpreter.stack := stack |>, host)
  | Some diff =>
    let diff := as_u64_saturated_macro diff in
    if i[diff] =? 0 then
      let stack :=
        number_stub.(RefStub.injection) interpreter.(Interpreter.stack) Impl_Uint.ZERO in
      (interpreter <| Interpreter.stack := stack |>, host)
    else if i[diff] <=? 256 then
      let requested_number := as_u64_saturated_macro requested_number in
      let '(hash_opt, host) := IHost.(Host.block_hash) host requested_number in
      match hash_opt with
      | None =>
        (halt_fatal interpreter, host)
      | Some hash =>
        let stack :=
          number_stub.(RefStub.injection)
            interpreter.(Interpreter.stack)
            (Impl_Uint.from_be_bytes hash.(fixed_FixedBytes.FixedBytes.value)) in
        (interpreter <| Interpreter.stack := stack |>, host)
      end
    else
      let stack :=
        number_stub.(RefStub.injection) interpreter.(Interpreter.stack) Impl_Uint.ZERO in
      (interpreter <| Interpreter.stack := stack |>, host)
  end).

Lemma blockhash_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_Host_for_H : Host.Run H H_types)
    `{IInterpreterTypes : !InterpreterTypes.C WIRE_types}
    `{InterpreterTypesEq :
      !InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes}
    `{IHost : !Host.C H H_types}
    `{HostEq : !Host.Eq.t IHost}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref (A := H) 1 in
  let context := {|
    instruction_context.InstructionContext.interpreter := ref_interpreter;
    instruction_context.InstructionContext.host := ref_host;
  |} in
  let result := blockhash interpreter host in
  {{
    SimulateM.eval_f
      (run_blockhash run_InterpreterTypes_for_WIRE run_Host_for_H context)
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      [fst result; snd result]%stack
    )
  }}.
Proof.
  intros.
  subst result.
  with_strategy transparent [run_blockhash] unfold blockhash, run_blockhash; cbn.
  popn_top_macro_eq InterpreterTypesEq.
  eapply Run.Call; [
    eapply Impl_Option.unwrap_unchecked_eq;
    reflexivity
  |].
  cbn.
  s.
  - eapply Run.Call.
    + eapply (HostEq.(Host.Eq.block_number)
        host
        [interpreter<| Interpreter.stack := s |>; host; tt; t0.(RefStub.projection) s]%stack
        (Ref.cast_to Pointer.Kind.Ref ref_host)).
      eapply (@CanRead.Mutable H H1 Pointer.Kind.Ref
        [interpreter<| Interpreter.stack := s |>; host; tt; t0.(RefStub.projection) s]%stack
        host
        (Ref.cast_to Pointer.Kind.Ref ref_host).(Ref.core)
        (@Stack.CanAccess.Mutable H H1
          [interpreter<| Interpreter.stack := s |>; host; tt; t0.(RefStub.projection) s]%stack
          1%nat
          H
          (Stack.Nth.ConsSucc H
            (interpreter<| Interpreter.stack := s |>)
            [host; tt; t0.(RefStub.projection) s]%stack
            0%nat
            (Stack.Nth.ConsZero H host [tt; t0.(RefStub.projection) s]%stack))
          []
          φ
          Some
          (fun _ new_value => Some new_value))).
      * reflexivity.
    + cbn.
      apply Run.Pure.
  - s. {
      apply Impl_Uint.checked_sub_eq.
    }
    destruct
      (Impl_Uint.checked_sub
        (IHost.(Host.block_number) host)
        (t0.(RefStub.projection) s)) as [diff|] eqn:H_diff;
      cbn.
    + unfold as_u64_saturated_macro.
      s; [
        eapply as_u64_saturated_macro_eq_at_stack
      |].
      s.
      destruct
        ((((diff.(Uint.value) / 2 ^ 64) mod 2 ^ 64 =? 0) &&
          ((diff.(Uint.value) / 2 ^ 128) mod 2 ^ 64 =? 0)) &&
          ((diff.(Uint.value) / 2 ^ 192) mod 2 ^ 64 =? 0))
        eqn:H_diff_fits.
      * destruct (diff.(Uint.value) mod 2 ^ 64 =? 0) eqn:H_diff_zero;
          cbn.
        { apply Run.LetUnfold.
          cbn.
          rewrite H_diff_zero.
          cbn.
          s. {
            rewrite H_diff_zero.
            cbn.
            apply Run.LetUnfold.
            cbn.
            s. {
              apply Impl_Uint.ZERO_eq.
            }
            s.
          }
        }
        destruct (diff.(Uint.value) mod 2 ^ 64 <=? 256) eqn:H_diff_history;
          cbn.
        { replace (Bool.eqb (diff.(Uint.value) mod 2 ^ 64 =? 0) true) with false
            by (rewrite H_diff_zero; reflexivity).
          cbn.
          repeat (apply Run.LetUnfold; cbn; try rewrite H_diff_zero; cbn).
          s.
          replace (Bool.eqb (diff.(Uint.value) mod 2 ^ 64 =? 0) true) with false
            by (rewrite H_diff_zero; reflexivity).
          cbn.
          s.
          replace (Bool.eqb (diff.(Uint.value) mod 2 ^ 64 <=? 256) true) with true
            by (rewrite H_diff_history; reflexivity).
          cbn.
          s; [
            s_apply Impl_Uint.as_limbs_eq
          |].
          s.
          destruct
            ((((t0.(RefStub.projection) s).(Uint.value) / 2 ^ 64) mod 2 ^ 64 =? 0) &&
              (((t0.(RefStub.projection) s).(Uint.value) / 2 ^ 128) mod 2 ^ 64 =? 0) &&
              (((t0.(RefStub.projection) s).(Uint.value) / 2 ^ 192) mod 2 ^ 64 =? 0))
            eqn:H_requested_number_fits;
            cbn.
          - eapply Run.Call
              with
                (output_inter :=
                  fst
                    (IHost.(Host.block_hash) host
                      ((t0.(RefStub.projection) s).(Uint.value) mod 2 ^ 64)))
                (stack_inter :=
                  [interpreter<| Interpreter.stack := s |>;
                   snd
                     (IHost.(Host.block_hash) host
                       ((t0.(RefStub.projection) s).(Uint.value) mod 2 ^ 64));
                   tt; t0.(RefStub.projection) s;
                   IHost.(Host.block_number) host;
                   (diff.(Uint.value) mod 2 ^ 64 : u64); tt]%stack).
            + change (Ref.cast_to Pointer.Kind.MutRef ref_host)
                with
                  (@Ref.cast_to H H1 Pointer.Kind.MutRef
                    Pointer.Kind.MutRef (make_ref (A := H) 1)).
              unfold aliases.B256.t in *.
              eapply (@block_hash_eval_eq
                H
                (Interpreter.t WIRE WIRE_types)
                H1
                H_types
                H3
                run_Host_for_H
                IHost
                HostEq
                (interpreter<| Interpreter.stack := s |>)
                host
                (make_ref (A := H) 1)
                ((t0.(RefStub.projection) s).(Uint.value) mod 2 ^ 64)
                [tt; t0.(RefStub.projection) s;
                 IHost.(Host.block_number) host;
                 (diff.(Uint.value) mod 2 ^ 64 : u64); tt]%stack).
              reflexivity.
            + cbn.
              destruct
                (IHost.(Host.block_hash) host
                  ((t0.(RefStub.projection) s).(Uint.value) mod 2 ^ 64))
                as [[hash|] host_after] eqn:H_block_hash;
                cbn.
              * s. {
                  apply Impl_Uint.from_be_bytes_eq.
                }
                s.
              * s. {
                  eapply halt_fatal_eq;
                  exact InterpreterTypesEq.
                }
                s.
          - s. {
              apply Impl_u64.max_eq.
            }
            eapply Run.Call
              with
                (output_inter := fst (IHost.(Host.block_hash) host Impl_u64.MAX))
                (stack_inter :=
                  [interpreter<| Interpreter.stack := s |>;
                   snd (IHost.(Host.block_hash) host Impl_u64.MAX);
                   tt; t0.(RefStub.projection) s;
                   IHost.(Host.block_number) host;
                   (diff.(Uint.value) mod 2 ^ 64 : u64); tt]%stack).
            + change (Ref.cast_to Pointer.Kind.MutRef ref_host)
                with
                  (@Ref.cast_to H H1 Pointer.Kind.MutRef
                    Pointer.Kind.MutRef (make_ref (A := H) 1)).
              unfold aliases.B256.t in *.
              eapply (@block_hash_eval_eq
                H
                (Interpreter.t WIRE WIRE_types)
                H1
                H_types
                H3
                run_Host_for_H
                IHost
                HostEq
                (interpreter<| Interpreter.stack := s |>)
                host
                (make_ref (A := H) 1)
                Impl_u64.MAX
                [tt; t0.(RefStub.projection) s;
                 IHost.(Host.block_number) host;
                 (diff.(Uint.value) mod 2 ^ 64 : u64); tt]%stack).
              reflexivity.
            + cbn.
              destruct (IHost.(Host.block_hash) host Impl_u64.MAX)
                as [[hash|] host_after] eqn:H_block_hash;
                cbn.
              * s. {
                  apply Impl_Uint.from_be_bytes_eq.
                }
                s.
              * s. {
                  eapply halt_fatal_eq;
                  exact InterpreterTypesEq.
                }
                s.
        }
        { replace (Bool.eqb (diff.(Uint.value) mod 2 ^ 64 =? 0) true) with false
            by (rewrite H_diff_zero; reflexivity).
          cbn.
          s.
          replace (Bool.eqb (diff.(Uint.value) mod 2 ^ 64 =? 0) true) with false
            by (rewrite H_diff_zero; reflexivity).
          cbn.
          s.
          replace (Bool.eqb (diff.(Uint.value) mod 2 ^ 64 <=? 256) true) with false
            by (rewrite H_diff_history; reflexivity).
          cbn.
          s; [
            apply Impl_Uint.ZERO_eq
          | s].
          all: rewrite H_diff_zero; reflexivity.
        }
      * replace (Bool.eqb false true) with false by reflexivity.
        cbn.
        s. {
          apply Impl_u64.max_eq.
        }
        s; [
          apply Impl_Uint.ZERO_eq
        | s].
        all: cbn; reflexivity.
    + s. {
        apply Impl_Uint.ZERO_eq.
      }
      s.
Qed.
