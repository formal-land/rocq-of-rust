Require Import simulate.RocqOfRust.
From Stdlib Require Import List Lia.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_context_interface.simulate.host_runtime.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.simulate.dispatch.
Require Import revm.revm_interpreter.simulate.runtime.
Require Import revm.revm_interpreter.instructions.simulate.runtime_host.

Section Routing.
  Context {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}.

  Definition canonical_execute (opcode : u8)
      (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :=
    let result := InterpreterDispatch.stateful opcode
      {| InstructionContext.State.interpreter := interpreter;
         InstructionContext.State.host := host |} in
    (InstructionContext.State.interpreter _ _ _ result,
      InstructionContext.State.host _ _ _ result).

  (** Routing treats instruction bodies as opaque; their adapter equalities
      are already proved separately. *)
  Local Opaque
    revm.revm_interpreter.instructions.simulate.arithmetic.add.add
    revm.revm_interpreter.instructions.simulate.arithmetic.addmod.addmod
    revm.revm_interpreter.instructions.simulate.arithmetic.div.div
    revm.revm_interpreter.instructions.simulate.arithmetic.exp.exp
    revm.revm_interpreter.instructions.simulate.arithmetic.mul.mul
    revm.revm_interpreter.instructions.simulate.arithmetic.mulmod.mulmod
    revm.revm_interpreter.instructions.simulate.arithmetic.rem.rem
    revm.revm_interpreter.instructions.simulate.arithmetic.sdiv.sdiv
    revm.revm_interpreter.instructions.simulate.arithmetic.signextend.signextend
    revm.revm_interpreter.instructions.simulate.arithmetic.smod.smod
    revm.revm_interpreter.instructions.simulate.arithmetic.sub.sub
    revm.revm_interpreter.instructions.simulate.bitwise.bitand.op_bitand
    revm.revm_interpreter.instructions.simulate.bitwise.bitor.op_bitor
    revm.revm_interpreter.instructions.simulate.bitwise.bitxor.op_bitxor
    revm.revm_interpreter.instructions.simulate.bitwise.byte.op_byte
    revm.revm_interpreter.instructions.simulate.bitwise.clz.op_clz
    revm.revm_interpreter.instructions.simulate.bitwise.eq.op_eq
    revm.revm_interpreter.instructions.simulate.bitwise.gt.op_gt
    revm.revm_interpreter.instructions.simulate.bitwise.iszero.op_iszero
    revm.revm_interpreter.instructions.simulate.bitwise.lt.op_lt
    revm.revm_interpreter.instructions.simulate.bitwise.not.op_not
    revm.revm_interpreter.instructions.simulate.bitwise.sar.op_sar
    revm.revm_interpreter.instructions.simulate.bitwise.sgt.op_sgt
    revm.revm_interpreter.instructions.simulate.bitwise.shl.op_shl
    revm.revm_interpreter.instructions.simulate.bitwise.shr.op_shr
    revm.revm_interpreter.instructions.simulate.bitwise.slt.op_slt
    revm.revm_interpreter.instructions.simulate.block_info.basefee.basefee
    revm.revm_interpreter.instructions.simulate.block_info.blob_basefee.blob_basefee
    revm.revm_interpreter.instructions.simulate.block_info.block_number.block_number
    revm.revm_interpreter.instructions.simulate.block_info.chainid.chainid
    revm.revm_interpreter.instructions.simulate.block_info.coinbase.coinbase
    revm.revm_interpreter.instructions.simulate.block_info.difficulty.difficulty
    revm.revm_interpreter.instructions.simulate.block_info.gaslimit.gaslimit
    revm.revm_interpreter.instructions.simulate.block_info.timestamp.timestamp
    revm.revm_interpreter.instructions.simulate.contract.call.call
    revm.revm_interpreter.instructions.simulate.contract.call_code.call_code
    revm.revm_interpreter.instructions.simulate.contract.create.create
    revm.revm_interpreter.instructions.simulate.contract.delegate_call.delegate_call
    revm.revm_interpreter.instructions.simulate.contract.static_call.static_call
    revm.revm_interpreter.instructions.simulate.control.invalid.invalid
    revm.revm_interpreter.instructions.simulate.control.jump.jump
    revm.revm_interpreter.instructions.simulate.control.jumpdest.jumpdest
    revm.revm_interpreter.instructions.simulate.control.jumpi.jumpi
    revm.revm_interpreter.instructions.simulate.control.pc.pc
    revm.revm_interpreter.instructions.simulate.control.ret.ret
    revm.revm_interpreter.instructions.simulate.control.revert.revert
    revm.revm_interpreter.instructions.simulate.control.stop.stop
    revm.revm_interpreter.instructions.simulate.control.unknown.unknown
    revm.revm_interpreter.instructions.simulate.host.balance.balance
    revm.revm_interpreter.instructions.simulate.host.blockhash.blockhash
    revm.revm_interpreter.instructions.simulate.host.extcodecopy.extcodecopy
    revm.revm_interpreter.instructions.simulate.host.extcodehash.extcodehash
    revm.revm_interpreter.instructions.simulate.host.extcodesize.extcodesize
    revm.revm_interpreter.instructions.simulate.host.log.log
    revm.revm_interpreter.instructions.simulate.host.selfbalance.selfbalance
    revm.revm_interpreter.instructions.simulate.host.selfdestruct.selfdestruct
    revm.revm_interpreter.instructions.simulate.host.sload.sload
    revm.revm_interpreter.instructions.simulate.host.sstore.sstore
    revm.revm_interpreter.instructions.simulate.host.tload.tload
    revm.revm_interpreter.instructions.simulate.host.tstore.tstore
    revm.revm_interpreter.instructions.simulate.memory.mcopy.mcopy
    revm.revm_interpreter.instructions.simulate.memory.mload.mload
    revm.revm_interpreter.instructions.simulate.memory.msize.msize
    revm.revm_interpreter.instructions.simulate.memory.mstore.mstore
    revm.revm_interpreter.instructions.simulate.memory.mstore8.mstore8
    revm.revm_interpreter.instructions.simulate.stack.dup.dup
    revm.revm_interpreter.instructions.simulate.stack.pop.pop
    revm.revm_interpreter.instructions.simulate.stack.push.push
    revm.revm_interpreter.instructions.simulate.stack.push0.push0
    revm.revm_interpreter.instructions.simulate.stack.swap.swap
    revm.revm_interpreter.instructions.simulate.system.address.address
    revm.revm_interpreter.instructions.simulate.system.calldatacopy.calldatacopy
    revm.revm_interpreter.instructions.simulate.system.calldataload.calldataload
    revm.revm_interpreter.instructions.simulate.system.calldatasize.calldatasize
    revm.revm_interpreter.instructions.simulate.system.caller.caller
    revm.revm_interpreter.instructions.simulate.system.callvalue.callvalue
    revm.revm_interpreter.instructions.simulate.system.codecopy.codecopy
    revm.revm_interpreter.instructions.simulate.system.codesize.codesize
    revm.revm_interpreter.instructions.simulate.system.gas.gas
    revm.revm_interpreter.instructions.simulate.system.keccak256.keccak256
    revm.revm_interpreter.instructions.simulate.system.returndatacopy.returndatacopy
    revm.revm_interpreter.instructions.simulate.system.returndatasize.returndatasize
    revm.revm_interpreter.instructions.simulate.tx_info.blob_hash.blob_hash
    revm.revm_interpreter.instructions.simulate.tx_info.gasprice.gasprice
    revm.revm_interpreter.instructions.simulate.tx_info.origin.origin
    RuntimeInstructions.basefee
    RuntimeInstructions.blob_basefee
    RuntimeInstructions.block_number
    RuntimeInstructions.chainid
    RuntimeInstructions.coinbase
    RuntimeInstructions.difficulty
    RuntimeInstructions.gaslimit
    RuntimeInstructions.timestamp
    RuntimeInstructions.call
    RuntimeInstructions.call_code
    RuntimeInstructions.create
    RuntimeInstructions.delegate_call
    RuntimeInstructions.static_call
    RuntimeInstructions.balance
    RuntimeInstructions.blockhash
    RuntimeInstructions.extcodecopy
    RuntimeInstructions.extcodehash
    RuntimeInstructions.extcodesize
    RuntimeInstructions.log
    RuntimeInstructions.selfbalance
    RuntimeInstructions.selfdestruct
    RuntimeInstructions.sload
    RuntimeInstructions.sstore
    RuntimeInstructions.tload
    RuntimeInstructions.tstore
    RuntimeInstructions.blob_hash
    RuntimeInstructions.gasprice
    RuntimeInstructions.origin.

  Create HintDb runtime_adapters.

  #[local] Hint Rewrite (RuntimeInstructions.basefee_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.blob_basefee_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.block_number_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.chainid_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.coinbase_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.difficulty_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.gaslimit_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.timestamp_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.call_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.call_code_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.create_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.delegate_call_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.static_call_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.balance_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.blockhash_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.extcodecopy_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.extcodehash_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.extcodesize_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.log_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.selfbalance_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.selfdestruct_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.sload_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.sstore_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.tload_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.tstore_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.blob_hash_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.gasprice_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes))
    (RuntimeInstructions.origin_eq (WIRE := WIRE) (IHost := IHost) (IInterpreterTypes := IInterpreterTypes)) : runtime_adapters.

  (** Check every opcode with arbitrary interpreter and host states. This also
      checks the unknown-opcode and PUSH/DUP/SWAP ranges. *)
  Lemma all_opcode_routes :
    Forall (fun byte => forall (interpreter : Interpreter.t WIRE WIRE_types) (host : H),
      RuntimeInstructionTable.execute (IHost := HostRuntime.of_linked IHost)
        {| Integer.value := Z.of_nat byte |} interpreter host =
      canonical_execute {| Integer.value := Z.of_nat byte |} interpreter host)
      (List.seq 0 256).
  Proof.
    cbn [List.seq].
    let rec check_routes := lazymatch goal with
    | |- Forall _ nil => constructor
    | _ => apply Forall_cons; [
      abstract (intros interpreter host;
      cbv beta iota zeta delta [RuntimeInstructionTable.execute canonical_execute
        InterpreterDispatch.stateful InterpreterDispatch.simple InstructionContext.map_interpreter
        InstructionContext.State.interpreter InstructionContext.State.host
        Integer.value Z.of_nat Pos.of_succ_nat Pos.succ Z.eqb Pos.eqb Z.leb Z.compare
        Pos.compare Pos.compare_cont andb];
      autorewrite with runtime_adapters;
      lazymatch goal with
      | |- (_, _) = _ => reflexivity
      | |- ?p = _ => destruct p; reflexivity
      end)
      | check_routes]
    end in check_routes.
  Qed.
End Routing.
