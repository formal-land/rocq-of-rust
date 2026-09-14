From Stdlib Require Import List ZArith.

Require Import revm.revm_interpreter.instructions.simulate.host.extcodecopy.
Require Import revm.revm_interpreter.instructions.simulate.host.extcodesize.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Section Input.
    Context (input : StatefulHost.Input.t).

    Definition account : StatefulHost.Account.t := {|
      StatefulHost.Account.address := 42;
      StatefulHost.Account.balance := 0;
      StatefulHost.Account.nonce := 1;
      StatefulHost.Account.code := [18; 52; 86];
      StatefulHost.Account.code_hash := 0;
      StatefulHost.Account.storage := [];
      StatefulHost.Account.transient_storage := [];
    |}.

    Definition run_external_with_gas (gas_limit : Z) (copy : bool) (spec : SpecId.t)
        (args warm_accounts : list Z) :=
      let interpreter : Interpreter.t WIRE WIRE_types :=
        (make_interpreter {| Stack.value := List.map (fun x => {| Uint.value := x |}) args |})
          <| @Interpreter.runtime_flag WIRE _ WIRE_types _ := spec |> in
      let interpreter : Interpreter.t WIRE WIRE_types :=
        interpreter <| @Interpreter.gas WIRE _ WIRE_types _ :=
          interpreter.(Interpreter.gas)
            <| Gas.limit := {| Integer.value := gas_limit |} |>
            <| Gas.remaining := {| Integer.value := gas_limit |} |> |> in
      let host := List.fold_left StatefulHost.warm_account warm_accounts
        (StatefulHost.with_accounts (StatefulHost.make input) [account]) in
      if copy then extcodecopy interpreter host else extcodesize interpreter host.

    Definition run_external := run_external_with_gas 1000000.

    Definition observe (result : Interpreter.t WIRE WIRE_types * StatefulHost.t) :=
      let '(interpreter, host) := result in
      (List.map Uint.value interpreter.(Interpreter.stack).(Stack.value),
       List.map Integer.value interpreter.(Interpreter.memory).(Memory.value),
       interpreter.(Interpreter.gas).(Gas.remaining).(Integer.value),
       host.(StatefulHost.accessed_accounts),
       match interpreter.(Interpreter.bytecode).(Bytecode.action) with
       | Some (InterpreterAction.Return result) => Some result.(InterpreterResult.result)
       | _ => None
       end).

    Lemma size_reads_nonempty_account_code :
      observe (run_external false SpecId.CANCUN [42] []) =
      ([3], [], 997400, [42], None).
    Proof. vm_compute. reflexivity. Qed.

    Lemma warm_size_costs_100 :
      observe (run_external false SpecId.CANCUN [42] [42]) =
      ([3], [], 999900, [42], None).
    Proof. vm_compute. reflexivity. Qed.

    Lemma absent_account_has_no_code :
      observe (run_external false SpecId.CANCUN [43] []) =
      ([0], [], 997400, [43], None).
    Proof. vm_compute. reflexivity. Qed.

    Lemma copy_reads_code_and_zero_pads :
      observe (run_external true SpecId.CANCUN [42; 1; 1; 4] []) =
      ([], [0; 52; 86; 0; 0] ++ List.repeat 0 27, 997394, [42], None).
    Proof. vm_compute. reflexivity. Qed.

    Lemma maximal_source_offset_copies_zeros :
      observe (run_external true SpecId.CANCUN [42; 0; 2 ^ 256 - 1; 1] []) =
      ([], List.repeat 0 32, 997394, [42], None).
    Proof. vm_compute. reflexivity. Qed.

    Lemma zero_length_ignores_memory_offset_but_charges_access :
      observe (run_external true SpecId.CANCUN [42; 2 ^ 256 - 1; 0; 0] []) =
      ([], [], 997400, [42], None).
    Proof. vm_compute. reflexivity. Qed.

    Lemma invalid_memory_offset_stops_before_account_access :
      observe (run_external true SpecId.CANCUN [42; 2 ^ 64; 0; 1] []) =
      ([], [], 999997, [], Some InstructionResult.InvalidOperandOOG).
    Proof. vm_compute. reflexivity. Qed.

    Lemma memory_expansion_failure_stops_before_account_access :
      observe (run_external true SpecId.CANCUN [42; 2 ^ 32; 0; 1] []) =
      ([], [], 999997, [], Some InstructionResult.MemoryOOG).
    Proof. vm_compute. reflexivity. Qed.

    Lemma copy_frontier_uses_legacy_code_loader :
      observe (run_external true SpecId.FRONTIER [42; 0; 0; 1] []) =
      ([], 18 :: List.repeat 0 31, 999974, [], None).
    Proof. vm_compute. reflexivity. Qed.

    Lemma size_tangerine_costs_700 :
      observe (run_external false SpecId.TANGERINE [42] []) =
      ([3], [], 999300, [42], None).
    Proof. vm_compute. reflexivity. Qed.

    Lemma copy_warm_account_exact_gas :
      observe (run_external_with_gas 106 true SpecId.CANCUN [42; 0; 0; 1] [42]) =
      ([], 18 :: List.repeat 0 31, 0, [42], None).
    Proof. vm_compute. reflexivity. Qed.

    Lemma size_insufficient_cold_gas_does_not_warm_account :
      observe (run_external_with_gas 2599 false SpecId.CANCUN [42] []) =
      ([42], [], 0, [], Some InstructionResult.OutOfGas).
    Proof. vm_compute. reflexivity. Qed.

    Lemma copy_insufficient_cold_gas_does_not_write_code :
      observe (run_external_with_gas 2605 true SpecId.CANCUN [42; 0; 0; 1] []) =
      ([], List.repeat 0 32, 0, [], Some InstructionResult.OutOfGas).
    Proof. vm_compute. reflexivity. Qed.

    Lemma copy_cost_failure_precedes_memory_and_account_access :
      observe (run_external_with_gas 2 true SpecId.CANCUN [42; 0; 0; 1] []) =
      ([], [], 0, [], Some InstructionResult.OutOfGas).
    Proof. vm_compute. reflexivity. Qed.

    Lemma size_underflow_does_not_access_account :
      observe (run_external false SpecId.CANCUN [] []) =
      ([], [], 1000000, [], Some InstructionResult.StackUnderflow).
    Proof. vm_compute. reflexivity. Qed.

    Lemma copy_underflow_preserves_stack :
      observe (run_external true SpecId.CANCUN [42; 0; 0] []) =
      ([42; 0; 0], [], 1000000, [], Some InstructionResult.StackUnderflow).
    Proof. vm_compute. reflexivity. Qed.

    Lemma size_warms_account_for_copy :
      let '(_, host) := run_external false SpecId.CANCUN [42] [] in
      let interpreter := make_interpreter
        {| Stack.value := List.map (fun x => {| Uint.value := x |}) [42; 0; 0; 1] |} in
      observe (extcodecopy interpreter host) =
      ([], 18 :: List.repeat 0 31, 999894, [42], None).
    Proof. vm_compute. reflexivity. Qed.

  End Input.
End Test.
