Require Import simulate.RocqOfRust.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_context_interface.simulate.host_runtime.
Require Import revm.revm_interpreter.instructions.simulate.host.sload.
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
Require Import revm.revm_interpreter.instructions.simulate.host.balance.
Require Import revm.revm_interpreter.instructions.simulate.host.blockhash.
Require Import revm.revm_interpreter.instructions.simulate.host.extcodecopy.
Require Import revm.revm_interpreter.instructions.simulate.host.extcodehash.
Require Import revm.revm_interpreter.instructions.simulate.host.extcodesize.
Require Import revm.revm_interpreter.instructions.simulate.host.log.
Require Import revm.revm_interpreter.instructions.simulate.host.selfbalance.
Require Import revm.revm_interpreter.instructions.simulate.host.selfdestruct.
Require Import revm.revm_interpreter.instructions.simulate.host.sstore.
Require Import revm.revm_interpreter.instructions.simulate.host.tload.
Require Import revm.revm_interpreter.instructions.simulate.host.tstore.
Require Import revm.revm_interpreter.instructions.simulate.tx_info.blob_hash.
Require Import revm.revm_interpreter.instructions.simulate.tx_info.gasprice.
Require Import revm.revm_interpreter.instructions.simulate.tx_info.origin.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.

(** Specialize only the host dictionary projections. The instruction body is
    obtained from its canonical definition, and the equalities below check each
    result against that definition for every linked host. *)
Ltac runtime_host_body body methods :=
  lazymatch body with
  | context C [@Host.load_account_info_skip_cold_load _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.load_account_info_skip_cold_load)] in
      runtime_host_body body methods
  | context C [@Host.load_account_code _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.load_account_code)] in
      runtime_host_body body methods
  | context C [@Host.block_hash _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.block_hash)] in
      runtime_host_body body methods
  | context C [@Host.max_initcode_size _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.max_initcode_size)] in
      runtime_host_body body methods
  | context C [@Host.beneficiary _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.beneficiary)] in
      runtime_host_body body methods
  | context C [@Host.block_number _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.block_number)] in
      runtime_host_body body methods
  | context C [@Host.timestamp _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.timestamp)] in
      runtime_host_body body methods
  | context C [@Host.gas_limit _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.gas_limit)] in
      runtime_host_body body methods
  | context C [@Host.chain_id _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.chain_id)] in
      runtime_host_body body methods
  | context C [@Host.basefee _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.basefee)] in
      runtime_host_body body methods
  | context C [@Host.blob_gasprice _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.blob_gasprice)] in
      runtime_host_body body methods
  | context C [@Host.effective_gas_price _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.effective_gas_price)] in
      runtime_host_body body methods
  | context C [@Host.caller _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.caller)] in
      runtime_host_body body methods
  | context C [@Host.blob_hash _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.blob_hash)] in
      runtime_host_body body methods
  | context C [@Host.difficulty _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.difficulty)] in
      runtime_host_body body methods
  | context C [@Host.prevrandao _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.prevrandao)] in
      runtime_host_body body methods
  | context C [@Host.balance _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.balance)] in
      runtime_host_body body methods
  | context C [@Host.sload _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.sload)] in
      runtime_host_body body methods
  | context C [@Host.sload_skip_cold_load _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.sload_skip_cold_load)] in
      runtime_host_body body methods
  | context C [@Host.sstore _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.sstore)] in
      runtime_host_body body methods
  | context C [@Host.sstore_skip_cold_load _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.sstore_skip_cold_load)] in
      runtime_host_body body methods
  | context C [@Host.tload _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.tload)] in
      runtime_host_body body methods
  | context C [@Host.tstore _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.tstore)] in
      runtime_host_body body methods
  | context C [@Host.log _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.log)] in
      runtime_host_body body methods
  | context C [@Host.selfdestruct _ _ _ _ _] =>
      let body := context C [methods.(HostRuntime.selfdestruct)] in
      runtime_host_body body methods
  | _ => lazymatch body with
      | (fun _ _ _ _ => ?body) => exact body
      end
  end.

Module RuntimeInstructions.
  Section Instructions.
    Context {WIRE H : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      {IInterpreterTypes : InterpreterTypes.C WIRE_types}
      {IHost : HostRuntime.C H}.

    Definition basefee (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @basefee.basefee WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [basefee.basefee] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition blob_basefee (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @blob_basefee.blob_basefee WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [blob_basefee.blob_basefee] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition block_number (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @block_number.block_number WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [block_number.block_number] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition chainid (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @chainid.chainid WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [chainid.chainid] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition coinbase (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @coinbase.coinbase WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [coinbase.coinbase] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition difficulty (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @difficulty.difficulty WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [difficulty.difficulty difficulty.difficulty_value] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition gaslimit (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @gaslimit.gaslimit WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [gaslimit.gaslimit] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition timestamp (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @timestamp.timestamp WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [timestamp.timestamp] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition call (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @call.call WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [call.call call_helpers.load_acc_and_calc_gas account_load.load_account_delegated] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition call_code (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @call_code.call_code WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [call_code.call_code call_helpers.load_acc_and_calc_gas account_load.load_account_delegated] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition create (IS_CREATE2 : bool) (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @create.create IS_CREATE2 WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [create.create create.finish_create] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition delegate_call (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @delegate_call.delegate_call WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [delegate_call.delegate_call call_helpers.load_acc_and_calc_gas account_load.load_account_delegated] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition static_call (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @static_call.static_call WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [static_call.static_call call_helpers.load_acc_and_calc_gas account_load.load_account_delegated] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition balance (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @balance.balance WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [balance.balance] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition blockhash (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @blockhash.blockhash WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [blockhash.blockhash] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition extcodecopy (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @extcodecopy.extcodecopy WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [extcodecopy.extcodecopy] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition extcodehash (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @extcodehash.extcodehash WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [extcodehash.extcodehash] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition extcodesize (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @extcodesize.extcodesize WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [extcodesize.extcodesize] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition log (N : usize) (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @log.log N WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [log.log log.finish_log] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition selfbalance (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @selfbalance.selfbalance WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [selfbalance.selfbalance] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition selfdestruct (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @selfdestruct.selfdestruct WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [selfdestruct.selfdestruct] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition sload (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @sload.sload WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [sload.sload] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition sstore (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @sstore.sstore WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [sstore.sstore] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition tload (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @tload.tload WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [tload.tload] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition tstore (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @tstore.tstore WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [tstore.tstore] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition blob_hash (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @blob_hash.blob_hash WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [blob_hash.blob_hash] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition gasprice (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @gasprice.gasprice WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [gasprice.gasprice] in raw in
      runtime_host_body body IHost.
    Defined.

    Definition origin (interpreter : Interpreter.t WIRE WIRE_types) (host : H)
        : Interpreter.t WIRE WIRE_types * H.
    Proof.
      let raw := constr:(fun (link : Link H) (types : Host.Types.t)
        (links : Host.Types.AreLinks types) (methods : @Host.C H link types links) =>
        @origin.origin WIRE H _ link WIRE_types _ IInterpreterTypes types links methods interpreter host) in
      let body := eval cbv beta iota zeta delta [origin.origin] in raw in
      runtime_host_body body IHost.
    Defined.

  End Instructions.

  Section Equalities.
    Context {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      {IInterpreterTypes : InterpreterTypes.C WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      {IHost : Host.C H H_types}.

    Lemma basefee_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      basefee (IHost := HostRuntime.of_linked IHost) interpreter host =
      basefee.basefee interpreter host.
    Proof. reflexivity. Qed.

    Lemma blob_basefee_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      blob_basefee (IHost := HostRuntime.of_linked IHost) interpreter host =
      blob_basefee.blob_basefee interpreter host.
    Proof. reflexivity. Qed.

    Lemma block_number_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      block_number (IHost := HostRuntime.of_linked IHost) interpreter host =
      block_number.block_number interpreter host.
    Proof. reflexivity. Qed.

    Lemma chainid_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      chainid (IHost := HostRuntime.of_linked IHost) interpreter host =
      chainid.chainid interpreter host.
    Proof. reflexivity. Qed.

    Lemma coinbase_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      coinbase (IHost := HostRuntime.of_linked IHost) interpreter host =
      coinbase.coinbase interpreter host.
    Proof. reflexivity. Qed.

    Lemma difficulty_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      difficulty (IHost := HostRuntime.of_linked IHost) interpreter host =
      difficulty.difficulty interpreter host.
    Proof. reflexivity. Qed.

    Lemma gaslimit_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      gaslimit (IHost := HostRuntime.of_linked IHost) interpreter host =
      gaslimit.gaslimit interpreter host.
    Proof. reflexivity. Qed.

    Lemma timestamp_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      timestamp (IHost := HostRuntime.of_linked IHost) interpreter host =
      timestamp.timestamp interpreter host.
    Proof. reflexivity. Qed.

    Lemma call_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      call (IHost := HostRuntime.of_linked IHost) interpreter host =
      call.call interpreter host.
    Proof. reflexivity. Qed.

    Lemma call_code_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      call_code (IHost := HostRuntime.of_linked IHost) interpreter host =
      call_code.call_code interpreter host.
    Proof. reflexivity. Qed.

    Lemma create_eq (IS_CREATE2 : bool) (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      create IS_CREATE2 (IHost := HostRuntime.of_linked IHost) interpreter host =
      create.create IS_CREATE2 interpreter host.
    Proof. reflexivity. Qed.

    Lemma delegate_call_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      delegate_call (IHost := HostRuntime.of_linked IHost) interpreter host =
      delegate_call.delegate_call interpreter host.
    Proof. reflexivity. Qed.

    Lemma static_call_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      static_call (IHost := HostRuntime.of_linked IHost) interpreter host =
      static_call.static_call interpreter host.
    Proof. reflexivity. Qed.

    Lemma balance_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      balance (IHost := HostRuntime.of_linked IHost) interpreter host =
      balance.balance interpreter host.
    Proof. reflexivity. Qed.

    Lemma blockhash_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      blockhash (IHost := HostRuntime.of_linked IHost) interpreter host =
      blockhash.blockhash interpreter host.
    Proof. reflexivity. Qed.

    Lemma extcodecopy_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      extcodecopy (IHost := HostRuntime.of_linked IHost) interpreter host =
      extcodecopy.extcodecopy interpreter host.
    Proof. reflexivity. Qed.

    Lemma extcodehash_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      extcodehash (IHost := HostRuntime.of_linked IHost) interpreter host =
      extcodehash.extcodehash interpreter host.
    Proof. reflexivity. Qed.

    Lemma extcodesize_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      extcodesize (IHost := HostRuntime.of_linked IHost) interpreter host =
      extcodesize.extcodesize interpreter host.
    Proof. reflexivity. Qed.

    Lemma log_eq (N : usize) (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      log N (IHost := HostRuntime.of_linked IHost) interpreter host =
      log.log N interpreter host.
    Proof. reflexivity. Qed.

    Lemma selfbalance_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      selfbalance (IHost := HostRuntime.of_linked IHost) interpreter host =
      selfbalance.selfbalance interpreter host.
    Proof. reflexivity. Qed.

    Lemma selfdestruct_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      selfdestruct (IHost := HostRuntime.of_linked IHost) interpreter host =
      selfdestruct.selfdestruct interpreter host.
    Proof. reflexivity. Qed.

    Lemma sload_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      sload (IHost := HostRuntime.of_linked IHost) interpreter host =
      sload.sload interpreter host.
    Proof. reflexivity. Qed.

    Lemma sstore_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      sstore (IHost := HostRuntime.of_linked IHost) interpreter host =
      sstore.sstore interpreter host.
    Proof. reflexivity. Qed.

    Lemma tload_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      tload (IHost := HostRuntime.of_linked IHost) interpreter host =
      tload.tload interpreter host.
    Proof. reflexivity. Qed.

    Lemma tstore_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      tstore (IHost := HostRuntime.of_linked IHost) interpreter host =
      tstore.tstore interpreter host.
    Proof. reflexivity. Qed.

    Lemma blob_hash_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      blob_hash (IHost := HostRuntime.of_linked IHost) interpreter host =
      blob_hash.blob_hash interpreter host.
    Proof. reflexivity. Qed.

    Lemma gasprice_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      gasprice (IHost := HostRuntime.of_linked IHost) interpreter host =
      gasprice.gasprice interpreter host.
    Proof. reflexivity. Qed.

    Lemma origin_eq (interpreter : Interpreter.t WIRE WIRE_types) (host : H) :
      origin (IHost := HostRuntime.of_linked IHost) interpreter host =
      origin.origin interpreter host.
    Proof. reflexivity. Qed.

  End Equalities.
End RuntimeInstructions.
