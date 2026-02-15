Require Import simulate.RocqOfRust.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.simulate.block.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.instructions.simulate.block_info.basefee.
Require Import revm.revm_interpreter.instructions.simulate.block_info.blob_basefee.
Require Import revm.revm_interpreter.instructions.simulate.block_info.block_number.
Require Import revm.revm_interpreter.instructions.simulate.block_info.chainid.
Require Import revm.revm_interpreter.instructions.simulate.block_info.coinbase.
Require Import revm.revm_interpreter.instructions.simulate.block_info.difficulty.
Require Import revm.revm_interpreter.instructions.simulate.block_info.gaslimit.
Require Import revm.revm_interpreter.instructions.simulate.block_info.timestamp.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.tests.host.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import ruint.links.lib.

(** ** block_number *)

(** Test that BLOCK_NUMBER pushes the block number (= 1) onto the stack *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := block_number interpreter host in
  result_interpreter.(Interpreter.stack).(Stack.value) = [{| Uint.value := 1 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** timestamp *)

(** Test that TIMESTAMP pushes the block timestamp (= 0) onto the stack *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := timestamp interpreter host in
  result_interpreter.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** basefee *)

(** Test that BASEFEE pushes the base fee (= 0) onto the stack.
    Requires LONDON spec (LATEST >= LONDON). *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := basefee interpreter host in
  result_interpreter.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** gaslimit *)

(** Test that GASLIMIT pushes the gas limit (= 0) onto the stack *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := gaslimit interpreter host in
  result_interpreter.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** coinbase *)

(** Test that COINBASE pushes the beneficiary address (= 0) as U256 onto the stack *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := coinbase interpreter host in
  result_interpreter.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** difficulty *)

(** Test that DIFFICULTY pushes prevrandao value onto the stack.
    LATEST spec >= MERGE, so it uses prevrandao (None -> ZERO). *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := difficulty interpreter host in
  result_interpreter.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** blob_basefee *)

(** Test that BLOBBASEFEE pushes the blob gas price onto the stack.
    LATEST spec >= CANCUN, blob_gasprice is None -> default 0. *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := blob_basefee interpreter host in
  result_interpreter.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** chainid *)

(** Test that CHAINID pushes the chain ID (= 1) onto the stack.
    Requires ISTANBUL spec (LATEST >= ISTANBUL). *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let host : TestHost.t := TestHost.Make in
  let '(result_interpreter, _) := chainid interpreter host in
  result_interpreter.(Interpreter.stack).(Stack.value) = [{| Uint.value := 1 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.
