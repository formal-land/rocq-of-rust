From Stdlib Require Import List ZArith.

Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.utils.simulate.keccak256.
Require Import bytes.links.bytes.
Require Import revm.revm_context_interface.links.cfg.
Require Import revm.revm_interpreter.interpreter.links.runtime_flags.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.interpreter_action.links.create_inputs.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.call_frame.
Require Import revm.revm_interpreter.tests.create_address.
Require Import revm.revm_interpreter.tests.frame.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module CreateFrame.
  Inductive preparation : Set :=
  | Immediate (output : InterpreterResult.t) (host : StatefulHost.t)
  | Child (address : Z) (checkpoint : StatefulHost.t) (state : CallFrame.state).

  Definition result (inputs : CreateInputs.t) (status : InstructionResult.t) :=
    {| InterpreterResult.result := status;
       InterpreterResult.output := Impl_Bytes.new;
       InterpreterResult.gas := Impl_Gas.new inputs.(CreateInputs.gas_limit) |}.

  Definition with_nonce (account : StatefulHost.Account.t) (nonce : Z) :=
    {| StatefulHost.Account.address := account.(StatefulHost.Account.address);
       StatefulHost.Account.balance := account.(StatefulHost.Account.balance);
       StatefulHost.Account.nonce := nonce;
       StatefulHost.Account.code := account.(StatefulHost.Account.code);
       StatefulHost.Account.code_hash := account.(StatefulHost.Account.code_hash);
       StatefulHost.Account.storage := account.(StatefulHost.Account.storage);
       StatefulHost.Account.transient_storage := account.(StatefulHost.Account.transient_storage) |}.

  Definition child (parent : CallFrame.machine) (address : Z)
      (inputs : CreateInputs.t) : CallFrame.machine :=
    let code := inputs.(CreateInputs.init_code)
      .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value) in
    let interpreter := make_interpreter_with_bytecode code {| Stack.value := [] |} in
    interpreter
      <| @Interpreter.runtime_flag WIRE _ WIRE_types _ :=
        parent.(Interpreter.runtime_flag) <| RuntimeFlags.is_static := false |> |>
      <| @Interpreter.gas WIRE _ WIRE_types _ := Impl_Gas.new inputs.(CreateInputs.gas_limit) |>
      <| @Interpreter.input WIRE _ WIRE_types _ :=
        {| Input.target_address := {| Address.value := address |};
           Input.caller_address := inputs.(CreateInputs.caller);
           Input.call_value := inputs.(CreateInputs.value);
           Input.input := CallInput.Bytes Impl_Bytes.new |} |>.

  (** Cancun/Prague creation entry, after instruction-level checks and gas. *)
  Definition prepare (parent : CallFrame.machine) (host : StatefulHost.t)
      (depth : nat) (inputs : CreateInputs.t) : option preparation :=
    if Nat.ltb 1024 depth then
      Some (Immediate (result inputs InstructionResult.CallTooDeep) host)
    else
      let caller := inputs.(CreateInputs.caller).(Address.value) in
      let host := StatefulHost.warm_account host caller in
      let account := match StatefulHost.find_account caller host.(StatefulHost.accounts) with
        | Some account => account | None => StatefulHost.empty_account caller end in
      let value := inputs.(CreateInputs.value).(Uint.value) in
      if account.(StatefulHost.Account.balance) <? value then
        Some (Immediate (result inputs InstructionResult.OutOfFunds) host)
      else
        let nonce := account.(StatefulHost.Account.nonce) in
        if 2 ^ 64 - 1 <=? nonce then
          Some (Immediate (result inputs InstructionResult.Return) host)
        else
          let address := match inputs.(CreateInputs.scheme) with
            | CreateScheme.Create => CreateAddress.create caller nonce
            | CreateScheme.Create2 salt => CreateAddress.create2 caller salt.(Uint.value)
                (List.map Integer.value inputs.(CreateInputs.init_code)
                  .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value))
            end in
          match address with
          | None => None
          | Some address =>
            let host := StatefulHost.with_accounts host
              (StatefulHost.update_account caller (fun account => with_nonce account (nonce + 1))
                host.(StatefulHost.accounts)) in
            let host := StatefulHost.append_change host (StatefulHost.Change.Nonce caller (nonce + 1)) in
            let checkpoint := StatefulHost.warm_account host address in
            let target := match StatefulHost.find_account address checkpoint.(StatefulHost.accounts) with
              | Some account => account | None => StatefulHost.empty_account address end in
            if negb (target.(StatefulHost.Account.code_hash) =? StatefulHost.empty_code_hash) ||
               negb (target.(StatefulHost.Account.nonce) =? 0) then
              Some (Immediate (result inputs InstructionResult.CreateCollision) checkpoint)
            else if 2 ^ 256 <=? target.(StatefulHost.Account.balance) + value then
              Some (Immediate (result inputs InstructionResult.OverflowPayment) checkpoint)
            else
              let accounts := StatefulHost.update_account caller
                (fun account => StatefulHost.account_with_balance account
                  (account.(StatefulHost.Account.balance) - value)) checkpoint.(StatefulHost.accounts) in
              let accounts := StatefulHost.update_account address
                (fun account =>
                  {| StatefulHost.Account.address := address;
                     StatefulHost.Account.balance := account.(StatefulHost.Account.balance) + value;
                     StatefulHost.Account.nonce := 1;
                     StatefulHost.Account.code := [];
                     StatefulHost.Account.code_hash := StatefulHost.empty_code_hash;
                     StatefulHost.Account.storage := [];
                     StatefulHost.Account.transient_storage := account.(StatefulHost.Account.transient_storage) |}) accounts in
              let host := StatefulHost.with_accounts checkpoint accounts in
              let host := StatefulHost.append_change host (StatefulHost.Change.Created address) in
              let host := StatefulHost.append_change host (StatefulHost.Change.Nonce address 1) in
              let host := StatefulHost.append_change host
                (StatefulHost.Change.Balance caller (account.(StatefulHost.Account.balance) - value)) in
              let host := StatefulHost.append_change host
                (StatefulHost.Change.Balance address (target.(StatefulHost.Account.balance) + value)) in
              Some (Child address checkpoint
                {| InstructionContext.State.interpreter := child parent address inputs;
                   InstructionContext.State.host := host |})
          end.

  Definition resume (parent : CallFrame.machine) (address : option Z)
      (output : InterpreterResult.t) : CallFrame.machine :=
    let success := StatefulFrame.successful output.(InterpreterResult.result) in
    let gas := if CallFrame.gas_returned output.(InterpreterResult.result) then
      Impl_Gas.erase_cost parent.(Interpreter.gas) output.(InterpreterResult.gas).(Gas.remaining)
      else parent.(Interpreter.gas) in
    let gas := if success then Impl_Gas.record_refund gas
      output.(InterpreterResult.gas).(Gas.refunded) else gas in
    parent
      <| @Interpreter.bytecode WIRE _ WIRE_types _ :=
        parent.(Interpreter.bytecode) <| Bytecode.action := None |> |>
      <| @Interpreter.stack WIRE _ WIRE_types _ :=
        {| Stack.value := {| Uint.value := if success then
            match address with Some address => address | None => 0 end else 0 |} ::
          parent.(Interpreter.stack).(Stack.value) |} |>
      <| @Interpreter.gas WIRE _ WIRE_types _ := gas |>
      <| @Interpreter.return_data WIRE _ WIRE_types _ :=
        match output.(InterpreterResult.result) with
        | InstructionResult.Revert => output.(InterpreterResult.output)
        | _ => Impl_Bytes.new
        end |>.

  Definition finish (address : Z) (checkpoint host : StatefulHost.t)
      (output : InterpreterResult.t) : InterpreterResult.t * StatefulHost.t :=
    if negb (StatefulFrame.successful output.(InterpreterResult.result)) then (output, checkpoint)
    else
      let code := List.map Integer.value output.(InterpreterResult.output)
        .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value) in
      let fail := fun status => (output <| InterpreterResult.result := status |>, checkpoint) in
      if match code with byte :: _ => byte =? 239 | [] => false end then
        fail InstructionResult.CreateContractStartingWithEF
      else if Nat.ltb 24576 (List.length code) then
        fail InstructionResult.CreateContractSizeLimit
      else match Impl_Gas.record_cost output.(InterpreterResult.gas)
        {| Integer.value := 200 * Z.of_nat (List.length code) |} with
      | None => fail InstructionResult.OutOfGas
      | Some gas =>
        let hash := List.fold_left (fun value byte => 256 * value + byte)
          (Keccak256.hash code) 0 in
        let accounts := StatefulHost.update_account address
          (fun account =>
            {| StatefulHost.Account.address := account.(StatefulHost.Account.address);
               StatefulHost.Account.balance := account.(StatefulHost.Account.balance);
               StatefulHost.Account.nonce := account.(StatefulHost.Account.nonce);
               StatefulHost.Account.code := code;
               StatefulHost.Account.code_hash := hash;
               StatefulHost.Account.storage := account.(StatefulHost.Account.storage);
               StatefulHost.Account.transient_storage := account.(StatefulHost.Account.transient_storage) |})
          host.(StatefulHost.accounts) in
        (output <| InterpreterResult.result := InstructionResult.Return |>
          <| InterpreterResult.gas := gas |>,
         StatefulHost.append_change (StatefulHost.with_accounts host accounts)
           (StatefulHost.Change.Code address code))
      end.
End CreateFrame.
