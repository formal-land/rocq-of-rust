From Stdlib Require Import List ZArith.

Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import bytes.links.bytes.
Require Import core.links.result.
Require Import core.num.simulate.mod.
Require Import revm.revm_interpreter.interpreter.links.runtime_flags.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.tests.call_frame.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_precompile.simulate.blake2.
Require Import revm.revm_precompile.simulate.bls12_381.g1_add.
Require Import revm.revm_precompile.simulate.bls12_381.g1_msm.
Require Import revm.revm_precompile.simulate.bls12_381.g2_add.
Require Import revm.revm_precompile.simulate.bls12_381.g2_msm.
Require Import revm.revm_precompile.simulate.bls12_381.map_fp2_to_g2.
Require Import revm.revm_precompile.simulate.bls12_381.map_fp_to_g1.
Require Import revm.revm_precompile.simulate.bls12_381.pairing.

Require Import revm.revm_precompile.simulate.bn254.
Require Import revm.revm_precompile.simulate.bn254_pairing_run.
Require Import revm.revm_precompile.simulate.interface.
Require Import revm.revm_precompile.simulate.kzg_point_evaluation.
Require Import revm.revm_precompile.simulate.modexp.
Require Import revm.revm_precompile.simulate.ripemd160.
Require Import revm.revm_precompile.simulate.secp256k1.
Require Import revm.revm_precompile.simulate.secp256r1.
Require Import revm.revm_precompile.simulate.sha256.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module PrecompileFrame.
  (** Native mainnet precompile sets for the public runner's supported forks.
      Recognition is separate from implementation: P256 and other missing
      implementations must never fall through to ordinary account bytecode. *)
  Definition addresses (spec : SpecId.t) : list Z :=
    match spec with
    | SpecId.FRONTIER | SpecId.FRONTIER_THAWING | SpecId.HOMESTEAD
    | SpecId.DAO_FORK | SpecId.TANGERINE | SpecId.SPURIOUS_DRAGON => [1; 2; 3; 4]
    | SpecId.BYZANTIUM | SpecId.CONSTANTINOPLE | SpecId.PETERSBURG =>
        List.map Z.of_nat (List.seq 1 8)
    | SpecId.ISTANBUL | SpecId.MUIR_GLACIER | SpecId.BERLIN | SpecId.LONDON
    | SpecId.ARROW_GLACIER | SpecId.GRAY_GLACIER | SpecId.MERGE | SpecId.SHANGHAI =>
        List.map Z.of_nat (List.seq 1 9)
    | SpecId.CANCUN => List.map Z.of_nat (List.seq 1 10)
    | SpecId.PRAGUE => List.map Z.of_nat (List.seq 1 17)
    | SpecId.OSAKA => List.map Z.of_nat (List.seq 1 17) ++ [256]
    | _ => []
    end.

  Definition is_precompile (spec : SpecId.t) (address : Z) : bool :=
    List.existsb (Z.eqb address) (addresses spec).

  (** Gas and output follow revm_precompile/{identity,hash}.rs; status and
      failure gas follow precompile_provider.rs. Children already own input. *)
  Definition linear_cost (base word : Z) (input : list u8) : Z :=
    (base + word * ((Z.of_nat (List.length input) + 31) / 32)) mod (2 ^ 64).

  Definition identity_cost := linear_cost 15 3.

  Definition sha256_cost := linear_cost 60 12.

  Definition ripemd160_cost := linear_cost 600 120.

  Definition complete (cost_of : list u8 -> Z)
      (output_of : alloy_primitives.bytes.links.mod.Bytes.t ->
        alloy_primitives.bytes.links.mod.Bytes.t)
      (child : CallFrame.machine) : InterpreterResult.t :=
    let input := match child.(Interpreter.input).(Input.input) with
      | CallInput.Bytes input => input
      | CallInput.SharedBuffer _ => Impl_Bytes.new
      end in
    let cost := cost_of input.(alloy_primitives.bytes.links.mod.Bytes.value)
      .(bytes.Bytes.value) in
    let gas := child.(Interpreter.gas) in
    if gas.(Gas.remaining).(Integer.value) <? cost then
      CallFrame.result InstructionResult.PrecompileOOG child
    else
      {| InterpreterResult.result := InstructionResult.Return;
         InterpreterResult.output := output_of input;
         InterpreterResult.gas := gas
           <| Gas.remaining := {| Integer.value := gas.(Gas.remaining).(Integer.value) - cost |} |> |}.

  Definition ecrecover := complete (fun _ => 3000) (fun input =>
    Impl_Bytes.copy_from_slice
      (List.map (fun byte => {| Integer.value := byte |})
        (Secp256k1.output (List.map Integer.value
          input.(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value))))).

  Definition identity := complete identity_cost (fun input => input).

  Definition sha256 := complete sha256_cost (fun input =>
    Impl_Bytes.copy_from_slice
      (List.map (fun byte => {| Integer.value := byte |})
        (Sha256.hash (List.map Integer.value
          input.(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value))))).

  Definition ripemd160 := complete ripemd160_cost (fun input =>
    Impl_Bytes.copy_from_slice
      (List.map (fun byte => {| Integer.value := byte |})
        (List.repeat 0 12 ++ Ripemd160.hash (List.map Integer.value
          input.(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value))))).

  Definition modexp (child : CallFrame.machine) : InterpreterResult.t :=
    let input := match child.(Interpreter.input).(Input.input) with
      | CallInput.Bytes input => input
      | CallInput.SharedBuffer _ => Impl_Bytes.new
      end in
    let gas := child.(Interpreter.gas) in
    let run_modexp :=
      if Impl_SpecId.is_enabled_in
        child.(Interpreter.runtime_flag).(RuntimeFlags.spec_id) SpecId.OSAKA
      then Modexp.run_osaka else
      if Impl_SpecId.is_enabled_in
        child.(Interpreter.runtime_flag).(RuntimeFlags.spec_id) SpecId.BERLIN
      then Modexp.run_berlin else Modexp.run_byzantium in
    match run_modexp
      (List.map Integer.value
        input.(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value))
      gas.(Gas.remaining).(Integer.value) with
    | Modexp.Result.Success cost output =>
      {| InterpreterResult.result := InstructionResult.Return;
         InterpreterResult.output := Impl_Bytes.copy_from_slice
           (List.map (fun byte => {| Integer.value := byte |}) output);
         InterpreterResult.gas := gas
           <| Gas.remaining := {| Integer.value := gas.(Gas.remaining).(Integer.value) - cost |} |> |}
    | Modexp.Result.OutOfGas => CallFrame.result InstructionResult.PrecompileOOG child
    | Modexp.Result.InvalidLength => CallFrame.result InstructionResult.PrecompileError child
    end.

  Definition blake2 (child : CallFrame.machine) : InterpreterResult.t :=
    let input := match child.(Interpreter.input).(Input.input) with
      | CallInput.Bytes input => input
      | CallInput.SharedBuffer _ => Impl_Bytes.new
      end in
    let gas := child.(Interpreter.gas) in
    match Blake2.run
      (List.map Integer.value
        input.(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value))
      gas.(Gas.remaining).(Integer.value) with
    | Blake2.Result.Success cost output =>
      {| InterpreterResult.result := InstructionResult.Return;
         InterpreterResult.output := Impl_Bytes.copy_from_slice
           (List.map (fun byte => {| Integer.value := byte |}) output);
         InterpreterResult.gas := gas
           <| Gas.remaining := {| Integer.value := gas.(Gas.remaining).(Integer.value) - cost |} |> |}
    | Blake2.Result.OutOfGas => CallFrame.result InstructionResult.PrecompileOOG child
    | _ => CallFrame.result InstructionResult.PrecompileError child
    end.

  Definition bn254 (multiply : bool) (child : CallFrame.machine) : InterpreterResult.t :=
    let input := match child.(Interpreter.input).(Input.input) with
      | CallInput.Bytes input => input
      | CallInput.SharedBuffer _ => Impl_Bytes.new
      end in
    let gas := child.(Interpreter.gas) in
    let istanbul := Impl_SpecId.is_enabled_in
      child.(Interpreter.runtime_flag).(RuntimeFlags.spec_id) SpecId.ISTANBUL in
    let cost := if multiply then (if istanbul then 6000 else 40000)
      else (if istanbul then 150 else 500) in
    let run := if multiply then Bn254.run_mul else Bn254.run_add in
    match run
      (List.map Integer.value
        input.(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value))
      cost gas.(Gas.remaining).(Integer.value) with
    | Bn254.Result.Success cost output =>
      {| InterpreterResult.result := InstructionResult.Return;
         InterpreterResult.output := Impl_Bytes.copy_from_slice
           (List.map (fun byte => {| Integer.value := byte |}) output);
         InterpreterResult.gas := gas
           <| Gas.remaining := {| Integer.value := gas.(Gas.remaining).(Integer.value) - cost |} |> |}
    | Bn254.Result.OutOfGas => CallFrame.result InstructionResult.PrecompileOOG child
    | Bn254.Result.InvalidPoint _ => CallFrame.result InstructionResult.PrecompileError child
    end.

  Definition bn254_pairing (child : CallFrame.machine) : InterpreterResult.t :=
    let input := match child.(Interpreter.input).(Input.input) with
      | CallInput.Bytes input => input
      | CallInput.SharedBuffer _ => Impl_Bytes.new
      end in
    let gas := child.(Interpreter.gas) in
    let istanbul := Impl_SpecId.is_enabled_in
      child.(Interpreter.runtime_flag).(RuntimeFlags.spec_id) SpecId.ISTANBUL in
    let base_cost := if istanbul then 45000 else 100000 in
    let pair_cost := if istanbul then 34000 else 80000 in
    match Bn254PairingRun.run base_cost pair_cost
      (List.map Integer.value
        input.(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value))
      gas.(Gas.remaining).(Integer.value) with
    | Bn254PairingRun.Result.Success cost output =>
      {| InterpreterResult.result := InstructionResult.Return;
         InterpreterResult.output := Impl_Bytes.copy_from_slice
           (List.map (fun byte => {| Integer.value := byte |}) output);
         InterpreterResult.gas := gas
           <| Gas.remaining := {| Integer.value := gas.(Gas.remaining).(Integer.value) - cost |} |> |}
    | Bn254PairingRun.Result.OutOfGas =>
      CallFrame.result InstructionResult.PrecompileOOG child
    | _ => CallFrame.result InstructionResult.PrecompileError child
    end.

  (** This adapter preserves unsupported crypto as None. A recognized address
      must never fall through to empty account bytecode in that case.
      CallFrame.child normalizes shared input to owned Bytes before dispatch. *)
  Definition partial_precompile (address : u64) (child : CallFrame.machine)
      : option InterpreterResult.t :=
    match child.(Interpreter.input).(Input.input) with
    | CallInput.SharedBuffer _ => None
    | CallInput.Bytes input =>
    let bytes := input.(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value) in
    let gas := child.(Interpreter.gas) in
    let limit := gas.(Gas.remaining) in
    let address := address.(Integer.value) in
    let result :=
      if Z.eqb address 10 then kzg_point_evaluation.run bytes limit else
      if Z.eqb address 11 then g1_add.g1_add bytes limit else
      if Z.eqb address 12 then g1_msm.g1_msm bytes limit else
      if Z.eqb address 13 then g2_add.g2_add bytes limit else
      if Z.eqb address 14 then g2_msm.g2_msm bytes limit else
      if Z.eqb address 15 then pairing.pairing bytes limit else
      if Z.eqb address 16 then map_fp_to_g1.map_fp_to_g1 bytes limit else
      if Z.eqb address 17 then map_fp2_to_g2.map_fp2_to_g2 bytes limit else
      if Z.eqb address 256 then secp256r1.p256_verify_osaka bytes limit else None in
    match result with
    | None => None
    | Some (Result.Err PrecompileError.OutOfGas) =>
      Some (CallFrame.result InstructionResult.PrecompileOOG child)
    | Some (Result.Err _) =>
      Some (CallFrame.result InstructionResult.PrecompileError child)
    | Some (Result.Ok output) =>
      if output.(PrecompileOutput.reverted) ||
        negb (Z.eqb output.(PrecompileOutput.gas_refunded).(Integer.value) 0)
      then None else
      match Impl_u64.checked_sub limit output.(PrecompileOutput.gas_used) with
      | None => Some (CallFrame.result InstructionResult.PrecompileOOG child)
      | Some remaining => Some
        {| InterpreterResult.result := InstructionResult.Return;
           InterpreterResult.output := output.(PrecompileOutput.bytes);
           InterpreterResult.gas := gas <| Gas.remaining := remaining |> |}
      end
    end
    end.

  (** A dispatcher exists for these addresses; individual requests can still
      be unsupported, as indicated by run returning None. *)
  Definition supported (address : Z) : bool :=
    (address =? 1) || (address =? 2) || (address =? 3) || (address =? 4) || (address =? 5) || (address =? 6) || (address =? 7) || (address =? 8) || (address =? 9) || (address =? 10) ||
    ((11 <=? address) && (address <=? 17)) || (address =? 256).

  Definition enabled (spec : SpecId.t) (address : Z) : bool :=
    is_precompile spec address && supported address.

  Definition run (address : Z) (child : CallFrame.machine) : option InterpreterResult.t :=
    if negb (is_precompile child.(Interpreter.runtime_flag).(RuntimeFlags.spec_id) address)
    then None else
    if address =? 1 then Some (ecrecover child) else
    if address =? 2 then Some (sha256 child) else
    if address =? 3 then Some (ripemd160 child) else
    if address =? 4 then Some (identity child) else
    if address =? 5 then Some (modexp child) else
    if ((address =? 6) || (address =? 7)) && is_precompile
      child.(Interpreter.runtime_flag).(RuntimeFlags.spec_id) address
    then Some (bn254 (address =? 7) child) else
    if (address =? 8) && is_precompile
      child.(Interpreter.runtime_flag).(RuntimeFlags.spec_id) address
    then Some (bn254_pairing child) else
    if (address =? 9) && is_precompile
      child.(Interpreter.runtime_flag).(RuntimeFlags.spec_id) address
    then Some (blake2 child) else
    partial_precompile {| Integer.value := address |} child.
End PrecompileFrame.
