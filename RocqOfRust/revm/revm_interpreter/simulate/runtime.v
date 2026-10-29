Require Import simulate.RocqOfRust.
From Stdlib Require Import List.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.simulate.host_runtime.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.table.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_interpreter.instructions.simulate.runtime_host.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.add.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.addmod.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.div.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.exp.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.mul.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.mulmod.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.rem.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.sdiv.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.signextend.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.smod.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.sub.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.bitand.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.bitor.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.bitxor.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.byte.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.clz.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.eq.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.gt.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.iszero.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.lt.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.not.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.sar.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.sgt.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.shl.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.shr.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.slt.
Require Import revm.revm_interpreter.instructions.simulate.block_info.basefee.
Require Import revm.revm_interpreter.instructions.simulate.block_info.blob_basefee.
Require Import revm.revm_interpreter.instructions.simulate.block_info.block_number.
Require Import revm.revm_interpreter.instructions.simulate.block_info.chainid.
Require Import revm.revm_interpreter.instructions.simulate.block_info.coinbase.
Require Import revm.revm_interpreter.instructions.simulate.block_info.difficulty.
Require Import revm.revm_interpreter.instructions.simulate.block_info.gaslimit.
Require Import revm.revm_interpreter.instructions.simulate.block_info.timestamp.
Require Import revm.revm_interpreter.instructions.simulate.contract.call.
Require Import revm.revm_interpreter.instructions.simulate.contract.call_code.
Require Import revm.revm_interpreter.instructions.simulate.contract.create.
Require Import revm.revm_interpreter.instructions.simulate.contract.delegate_call.
Require Import revm.revm_interpreter.instructions.simulate.contract.static_call.
Require Import revm.revm_interpreter.instructions.simulate.control.invalid.
Require Import revm.revm_interpreter.instructions.simulate.control.jump.
Require Import revm.revm_interpreter.instructions.simulate.control.jumpdest.
Require Import revm.revm_interpreter.instructions.simulate.control.jumpi.
Require Import revm.revm_interpreter.instructions.simulate.control.pc.
Require Import revm.revm_interpreter.instructions.simulate.control.ret.
Require Import revm.revm_interpreter.instructions.simulate.control.revert.
Require Import revm.revm_interpreter.instructions.simulate.control.stop.
Require Import revm.revm_interpreter.instructions.simulate.control.unknown.
Require Import revm.revm_interpreter.instructions.simulate.host.balance.
Require Import revm.revm_interpreter.instructions.simulate.host.blockhash.
Require Import revm.revm_interpreter.instructions.simulate.host.extcodecopy.
Require Import revm.revm_interpreter.instructions.simulate.host.extcodehash.
Require Import revm.revm_interpreter.instructions.simulate.host.extcodesize.
Require Import revm.revm_interpreter.instructions.simulate.host.log.
Require Import revm.revm_interpreter.instructions.simulate.host.selfbalance.
Require Import revm.revm_interpreter.instructions.simulate.host.selfdestruct.
Require Import revm.revm_interpreter.instructions.simulate.host.sload.
Require Import revm.revm_interpreter.instructions.simulate.host.sstore.
Require Import revm.revm_interpreter.instructions.simulate.host.tload.
Require Import revm.revm_interpreter.instructions.simulate.host.tstore.
Require Import revm.revm_interpreter.instructions.simulate.memory.mcopy.
Require Import revm.revm_interpreter.instructions.simulate.memory.mload.
Require Import revm.revm_interpreter.instructions.simulate.memory.msize.
Require Import revm.revm_interpreter.instructions.simulate.memory.mstore.
Require Import revm.revm_interpreter.instructions.simulate.memory.mstore8.
Require Import revm.revm_interpreter.instructions.simulate.stack.dup.
Require Import revm.revm_interpreter.instructions.simulate.stack.pop.
Require Import revm.revm_interpreter.instructions.simulate.stack.push.
Require Import revm.revm_interpreter.instructions.simulate.stack.push0.
Require Import revm.revm_interpreter.instructions.simulate.stack.swap.
Require Import revm.revm_interpreter.instructions.simulate.system.address.
Require Import revm.revm_interpreter.instructions.simulate.system.calldatacopy.
Require Import revm.revm_interpreter.instructions.simulate.system.calldataload.
Require Import revm.revm_interpreter.instructions.simulate.system.calldatasize.
Require Import revm.revm_interpreter.instructions.simulate.system.caller.
Require Import revm.revm_interpreter.instructions.simulate.system.callvalue.
Require Import revm.revm_interpreter.instructions.simulate.system.codecopy.
Require Import revm.revm_interpreter.instructions.simulate.system.codesize.
Require Import revm.revm_interpreter.instructions.simulate.system.gas.
Require Import revm.revm_interpreter.instructions.simulate.system.keccak256.
Require Import revm.revm_interpreter.instructions.simulate.system.returndatacopy.
Require Import revm.revm_interpreter.instructions.simulate.system.returndatasize.
Require Import revm.revm_interpreter.instructions.simulate.table.
Require Import revm.revm_interpreter.instructions.simulate.tx_info.blob_hash.
Require Import revm.revm_interpreter.instructions.simulate.tx_info.gasprice.
Require Import revm.revm_interpreter.instructions.simulate.tx_info.origin.

Module RuntimeInstructionTable.
  (** Project static gas from the canonical instruction table. All link and
      function-pointer arguments disappear during this computation. *)
  Definition gas_schedule : list u64.
  Proof.
    let raw := constr:(fun (WIRE H : Set) (wire_link : Link WIRE) (host_link : Link H)
      (wire_types : InterpreterTypes.Types.t) (wire_links : InterpreterTypes.Types.AreLinks wire_types)
      (host_types : Host.Types.t) (host_links : Host.Types.AreLinks host_types)
      (wire_methods : @InterpreterTypes.Run WIRE wire_link wire_types wire_links)
      (host_methods : @Host.Run H host_link host_types host_links) =>
      List.map (@Instruction.static_gas WIRE H wire_link host_link wire_types wire_links)
        (ArrayPairs.to_list (@FragmentInstructionTable.table WIRE H wire_link host_link
          wire_types wire_links host_types host_links wire_methods host_methods).(array.value))) in
    let body := eval vm_compute in raw in
    lazymatch body with (fun _ _ _ _ _ _ _ _ _ _ => ?schedule) => exact schedule end.
  Defined.

  (** instructions.rs::instruction_table_impl. Host-free instructions retain
      their canonical bodies; host operations use the proved dictionary adapters. *)
  Definition execute
      {WIRE H : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      {IInterpreterTypes : InterpreterTypes.C WIRE_types} {IHost : HostRuntime.C H}
      (opcode : u8) (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
      : Interpreter.t WIRE WIRE_types * H :=
    let plain (operation : Interpreter.t WIRE WIRE_types -> Interpreter.t WIRE WIRE_types) :=
      (operation interpreter, host) in
    let byte := opcode.(Integer.value) in
    if Z.eqb byte 0 then plain (stop) else
    if Z.eqb byte 1 then plain (add) else
    if Z.eqb byte 2 then plain (mul) else
    if Z.eqb byte 3 then plain (sub) else
    if Z.eqb byte 4 then plain (div) else
    if Z.eqb byte 5 then plain (sdiv) else
    if Z.eqb byte 6 then plain (rem) else
    if Z.eqb byte 7 then plain (smod) else
    if Z.eqb byte 8 then plain (addmod) else
    if Z.eqb byte 9 then plain (mulmod) else
    if Z.eqb byte 10 then plain (exp IInterpreterTypes) else
    if Z.eqb byte 11 then plain (signextend) else
    if Z.eqb byte 16 then plain (op_lt) else
    if Z.eqb byte 17 then plain (op_gt) else
    if Z.eqb byte 18 then plain (op_slt) else
    if Z.eqb byte 19 then plain (op_sgt) else
    if Z.eqb byte 20 then plain (op_eq) else
    if Z.eqb byte 21 then plain (op_iszero) else
    if Z.eqb byte 22 then plain (op_bitand) else
    if Z.eqb byte 23 then plain (op_bitor) else
    if Z.eqb byte 24 then plain (op_bitxor) else
    if Z.eqb byte 25 then plain (op_not) else
    if Z.eqb byte 26 then plain (op_byte) else
    if Z.eqb byte 27 then plain (op_shl) else
    if Z.eqb byte 28 then plain (op_shr) else
    if Z.eqb byte 29 then plain (op_sar) else
    if Z.eqb byte 30 then plain (op_clz) else
    if Z.eqb byte 32 then plain (keccak256) else
    if Z.eqb byte 48 then plain (address) else
    if Z.eqb byte 49 then RuntimeInstructions.balance interpreter host else
    if Z.eqb byte 50 then RuntimeInstructions.origin interpreter host else
    if Z.eqb byte 51 then plain (caller) else
    if Z.eqb byte 52 then plain (callvalue) else
    if Z.eqb byte 53 then plain (calldataload) else
    if Z.eqb byte 54 then plain (calldatasize) else
    if Z.eqb byte 55 then plain (calldatacopy) else
    if Z.eqb byte 56 then plain (codesize) else
    if Z.eqb byte 57 then plain (codecopy) else
    if Z.eqb byte 58 then RuntimeInstructions.gasprice interpreter host else
    if Z.eqb byte 59 then RuntimeInstructions.extcodesize interpreter host else
    if Z.eqb byte 60 then RuntimeInstructions.extcodecopy interpreter host else
    if Z.eqb byte 61 then plain (returndatasize) else
    if Z.eqb byte 62 then plain (returndatacopy) else
    if Z.eqb byte 63 then RuntimeInstructions.extcodehash interpreter host else
    if Z.eqb byte 64 then RuntimeInstructions.blockhash interpreter host else
    if Z.eqb byte 65 then RuntimeInstructions.coinbase interpreter host else
    if Z.eqb byte 66 then RuntimeInstructions.timestamp interpreter host else
    if Z.eqb byte 67 then RuntimeInstructions.block_number interpreter host else
    if Z.eqb byte 68 then RuntimeInstructions.difficulty interpreter host else
    if Z.eqb byte 69 then RuntimeInstructions.gaslimit interpreter host else
    if Z.eqb byte 70 then RuntimeInstructions.chainid interpreter host else
    if Z.eqb byte 71 then RuntimeInstructions.selfbalance interpreter host else
    if Z.eqb byte 72 then RuntimeInstructions.basefee interpreter host else
    if Z.eqb byte 73 then RuntimeInstructions.blob_hash interpreter host else
    if Z.eqb byte 74 then RuntimeInstructions.blob_basefee interpreter host else
    if Z.eqb byte 80 then plain (pop) else
    if Z.eqb byte 81 then plain (mload) else
    if Z.eqb byte 82 then plain (mstore) else
    if Z.eqb byte 83 then plain (mstore8) else
    if Z.eqb byte 84 then RuntimeInstructions.sload interpreter host else
    if Z.eqb byte 85 then RuntimeInstructions.sstore interpreter host else
    if Z.eqb byte 86 then plain (jump) else
    if Z.eqb byte 87 then plain (jumpi) else
    if Z.eqb byte 88 then plain (pc) else
    if Z.eqb byte 89 then plain (msize) else
    if Z.eqb byte 90 then plain (gas) else
    if Z.eqb byte 91 then plain (jumpdest) else
    if Z.eqb byte 92 then RuntimeInstructions.tload interpreter host else
    if Z.eqb byte 93 then RuntimeInstructions.tstore interpreter host else
    if Z.eqb byte 94 then plain (mcopy) else
    if Z.eqb byte 95 then plain (push0) else
    if Z.eqb byte 160 then RuntimeInstructions.log 0 interpreter host else
    if Z.eqb byte 161 then RuntimeInstructions.log 1 interpreter host else
    if Z.eqb byte 162 then RuntimeInstructions.log 2 interpreter host else
    if Z.eqb byte 163 then RuntimeInstructions.log 3 interpreter host else
    if Z.eqb byte 164 then RuntimeInstructions.log 4 interpreter host else
    if Z.eqb byte 240 then RuntimeInstructions.create false interpreter host else
    if Z.eqb byte 241 then RuntimeInstructions.call interpreter host else
    if Z.eqb byte 242 then RuntimeInstructions.call_code interpreter host else
    if Z.eqb byte 243 then plain (ret) else
    if Z.eqb byte 244 then RuntimeInstructions.delegate_call interpreter host else
    if Z.eqb byte 245 then RuntimeInstructions.create true interpreter host else
    if Z.eqb byte 250 then RuntimeInstructions.static_call interpreter host else
    if Z.eqb byte 253 then plain (revert) else
    if Z.eqb byte 254 then plain (invalid) else
    if Z.eqb byte 255 then RuntimeInstructions.selfdestruct interpreter host else
    if Z.leb 96 byte && Z.leb byte 127 then plain (push {| Integer.value := byte - 95 |}) else
    if Z.leb 128 byte && Z.leb byte 143 then plain (dup {| Integer.value := byte - 127 |}) else
    if Z.leb 144 byte && Z.leb byte 159 then plain (swap {| Integer.value := byte - 143 |}) else
    plain unknown.
End RuntimeInstructionTable.

Module RuntimeInterpreter.
  Definition step
      {WIRE H : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      {IInterpreterTypes : InterpreterTypes.C WIRE_types} {IHost : HostRuntime.C H}
      (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
      : option (Interpreter.t WIRE WIRE_types * H) :=
    let jumps := IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode) in
    let opcode := jumps.(Jumps.opcode) interpreter.(Interpreter.bytecode) in
    let interpreter := interpreter <| Interpreter.bytecode :=
      jumps.(Jumps.relative_jump) interpreter.(Interpreter.bytecode) 1 |> in
    if Z.leb 0 opcode.(Integer.value) && Z.ltb opcode.(Integer.value) 256 then
      match List.nth_error RuntimeInstructionTable.gas_schedule (Z.to_nat opcode.(Integer.value)) with
      | None => None
      | Some static_gas =>
        match Impl_Gas.record_cost interpreter.(Interpreter.gas) static_gas with
        | None => Some (halt_oog interpreter, host)
        | Some gas => Some (RuntimeInstructionTable.execute opcode
            (interpreter <| Interpreter.gas := gas |>) host)
        end
      end
    else None.

  (** Fuel is an evaluator bound, not part of Rust's execution state. The
      remaining bound is returned so nested frames share one budget. *)
  Fixpoint run_plain
      {WIRE H : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      {IInterpreterTypes : InterpreterTypes.C WIRE_types} {IHost : HostRuntime.C H}
      (fuel : nat) (is_not_end : WIRE_types.(InterpreterTypes.Types.Bytecode) -> bool)
      (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
      : option (InterpreterAction.t * Interpreter.t WIRE WIRE_types * H * nat) :=
    if is_not_end interpreter.(Interpreter.bytecode) then
      match fuel with
      | O => None
      | S fuel => match step interpreter host with
          | None => None
          | Some (interpreter, host) => run_plain fuel is_not_end interpreter host
          end
      end
    else
      let '(action, bytecode) := IInterpreterTypes.(InterpreterTypes.LoopControl_for_Bytecode)
        .(LoopControl.take_next_action) interpreter.(Interpreter.bytecode) in
      Some (action, interpreter <| Interpreter.bytecode := bytecode |>, host, fuel).
End RuntimeInterpreter.
