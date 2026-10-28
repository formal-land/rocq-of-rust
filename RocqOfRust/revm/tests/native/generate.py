from pathlib import Path
import re
from generate_context import (generate_context, generate_context_handlers,
                              generate_context_runtime, generate_context_transactions)

def generate_transaction_smoke(root, output):
    p = output
    code = (root/'revm/tests/native/templates/normalization_imports.v.in').read_text()
    code += """Require Import NativeTransactions.
Require Import RocqOfRust.revm.revm_handler.tests.transaction_cases.
Require Import RocqOfRust.revm.revm_handler.simulate.transaction_accounting.
Require Import RocqOfRust.revm.revm_interpreter.links.instruction_result.
Require Import RocqOfRust.revm.revm_primitives.links.hardfork.
Require Import RocqOfRust.alloy_primitives.utils.simulate.keccak256.
Require Import RocqOfRust.revm.revm_precompile.simulate.modexp.
Import ListNotations.
Open Scope Z_scope.
Module NativeTxTest.
Import TransactionCases.
"""
    code+='''
     Definition check_observation (status : InstructionResult.t)
         (gas nonce sender target coinbase slot : Z) (result : EestTypes.Result.t) : bool :=
      match observation result with
      | Some (status', gas', nonce', sender', target', coinbase', slot') =>
        let status_ok := match status, status' with
        | InstructionResult.Stop, InstructionResult.Stop
        | InstructionResult.Revert, InstructionResult.Revert
        | InstructionResult.InvalidFEOpcode, InstructionResult.InvalidFEOpcode => true
        | _, _ => false end in
        status_ok && (gas =? gas') && (nonce =? nonce') && (sender =? sender') &&
          (target =? target') && (coinbase =? coinbase') && (slot =? slot')
      | None => false
      end.
    '''
    scenarios=[
     ('legacy_stop','SpecId.CANCUN','tx','input [0]','Stop',[21000,1,789993,7,126000,1]),
     ('legacy_revert','SpecId.CANCUN','tx','input [95;95;253]','Revert',[21004,1,789960,0,126024,1]),
     ('dynamic_stop','SpecId.CANCUN','dynamic_fee_tx','input [0]','Stop',[21000,1,873993,7,42000,1]),
     ('dynamic_gasprice','SpecId.CANCUN','dynamic_fee_tx','input [58;95;85;0]','Stop',[26004,1,843969,7,52008,6]),
     ('access_duplicates','SpecId.CANCUN','access_list_tx [(42,[0;0]);(42,[0])]','input [95;84;80;0]','Stop',[31604,1,683953,7,189624,1]),
     ('dynamic_revert','SpecId.PRAGUE','dynamic_fee_tx','input [95;95;253]','Revert',[21004,1,873976,0,42008,1]),
     ('dynamic_halt','SpecId.OSAKA','dynamic_fee_tx','input [254]','InvalidFEOpcode',[50000,1,700000,0,100000,1]),
     ('blob_stop','SpecId.CANCUN','blob_tx','blob_input [0]','Stop',[21000,1,611849,7,42000,1]),
     ('blob_hash','SpecId.CANCUN','blob_tx','blob_input [95;73;95;85;0]','Stop',[26007,1,581807,7,52014,'blob_hash'])]
    names=[]
    for name,spec,tx,input_,status,values in scenarios:
     ident='native_smoke_'+name;names.append(ident)
     code+=f'Definition {ident} := check_observation InstructionResult.{status} '+ ' '.join(map(str,values))+f' (native_transaction_run 100 {spec} ({tx}) ({input_})).\n'
    for name,tx,reason in [
     ('dynamic_affordability','dynamic_fee_tx <| TransactionAccounting.Transaction.gas_price := 30 |>','LackOfFunds'),
     ('nonce_precedence','dynamic_fee_tx <| TransactionAccounting.Transaction.gas_price := 2^128-1 |> <| TransactionAccounting.Transaction.nonce := 1 |>','NonceTooHigh'),
     ('missing_chain','dynamic_fee_tx <| TransactionAccounting.Transaction.chain_id := None |>','MissingChainId')]:
     ident='native_smoke_'+name;names.append(ident)
     code+=f'''Definition {ident} :=
     match native_transaction_run 100 SpecId.CANCUN ({tx}) (input [0]) with
     | EestTypes.Result.Rejected EestTypes.Rejection.{reason} => true
     | _ => false end.
    '''
    code += """End NativeTxTest.
Module NativeCreateTest.
Import CreationCases.
Definition run (init_code : list Z) :=
  native_transaction_run 100 SpecId.CANCUN (tx init_code) input.
"""
    code+='''Definition check_creation (deploy : bool) (gas sender coinbase : Z) (result : EestTypes.Result.t) :=
     match observation result with
     | Some (InstructionResult.Return, gas', nonce, sender', coinbase',
         Some (created_nonce, created_value, created_code, [], []), output, []) =>
       let code_ok := match deploy, created_code, output with
       | false, [], [] => true
       | true, [byte], [out_byte] => (byte =? 0) && (out_byte =? 0)
       | _, _, _ => false end in
       code_ok && (gas =? gas') && (nonce =? 1) && (sender =? sender') &&
         (coinbase =? coinbase') && (created_nonce =? 1) && (created_value =? 7)
     | _ => false end.
    Definition native_smoke_create_empty := check_creation false 53006 469933 318036 (run [0]).
    Definition native_smoke_create_deploy := check_creation true 53334 466653 320004 (run [96;0;95;83;96;1;95;243]).
    End NativeCreateTest.
    Set Extraction KeepSingleton.
    Extraction Language OCaml.
    '''
    recovery_source = (root/'revm/revm_precompile/tests/secp256k1.v').read_text()
    code += 'Module NativeEcrecoverTest.\n'
    for name in ['input_words', 'valid_key_input', 'valid_output', 'invalid_high_v_1_input']:
        definition = re.search(
            r'^  Definition ' + name + r'\b.*?(?=^  (?:Definition|Lemma)|\Z)',
            recovery_source, re.MULTILINE | re.DOTALL,
        )
        if definition is None:
            raise ValueError(f'Missing ECRECOVER regression definition {name}')
        code += definition.group() + '\n'
    code += '''Fixpoint bytes_eq (left right : list Z) : bool :=
      match left, right with
      | [], [] => true
      | byte :: rest, other :: others => (byte =? other) && bytes_eq rest others
      | _, _ => false
      end.
    Definition run (data : list Z) := native_transaction_run 100 SpecId.CANCUN
      (TransactionCases.tx <| TransactionAccounting.Transaction.target := Some 1 |>
        <| TransactionAccounting.Transaction.data := data |>) (TransactionCases.input []).
    Definition check_precompile (expected : list Z) (used sender_balance reward : Z)
        (result : EestTypes.Result.t) : bool :=
      match result with
      | EestTypes.Result.Completed output =>
        let gas := output.(EestTypes.Output.gas) in
        let sender := EestTypes.account_at 100 output.(EestTypes.Output.accounts) in
        let target := EestTypes.account_at 1 output.(EestTypes.Output.accounts) in
        let coinbase := EestTypes.account_at 99 output.(EestTypes.Output.accounts) in
        let returned := match output.(EestTypes.Output.status) with
          | InstructionResult.Return => true | _ => false end in
        returned && bytes_eq output.(EestTypes.Output.data) expected &&
          (gas.(TransactionAccounting.Settlement.gas_used) =? used) &&
          (gas.(TransactionAccounting.Settlement.gas_remaining) =? 50000 - used) &&
          (gas.(TransactionAccounting.Settlement.gas_refunded) =? 0) &&
          (gas.(TransactionAccounting.Settlement.caller_reimbursement) =? (50000 - used) * 10) &&
          (gas.(TransactionAccounting.Settlement.beneficiary_reward) =? reward) &&
          (gas.(TransactionAccounting.Settlement.base_fee_burn) =? used * 4) &&
          (gas.(TransactionAccounting.Settlement.blob_fee_burn) =? 0) &&
          (sender.(EestTypes.Account.nonce) =? 1) &&
          (sender.(EestTypes.Account.balance) =? sender_balance) &&
          (target.(EestTypes.Account.balance) =? 7) &&
          (coinbase.(EestTypes.Account.balance) =? reward)
      | _ => false
      end.
    Definition native_smoke_ecrecover_valid :=
      check_precompile valid_output 25676 743233 154056 (run valid_key_input).
    Definition native_smoke_ecrecover_invalid :=
      check_precompile [] 25688 743113 154128 (run invalid_high_v_1_input).
    End NativeEcrecoverTest.
    '''
    recovery_names = ['native_smoke_ecrecover_valid', 'native_smoke_ecrecover_invalid']
    # Copy definitions only, so native checks do not depend on the expensive
    # vm_compute proofs in the source test module.
    p256_source = (root/'revm/revm_precompile/tests/secp256r1_verification.v').read_text()
    p256_definitions = re.findall(
        r'^  Definition (\w+)\b.*?(?=^  (?:Definition|Example)|^End )',
        p256_source, re.MULTILINE | re.DOTALL,
    )
    p256_names = [name for name in p256_definitions if name.endswith('_check')]
    if len(p256_names) != 35 or 'input_bytes' not in p256_definitions:
        raise ValueError('Expected input_bytes and 35 P256 regression checks')
    code += 'Require Import RocqOfRust.revm.revm_precompile.simulate.secp256r1.\n'
    code += 'Module NativeP256Test.\n'
    for name in p256_definitions:
        definition = re.search(
            r'^  Definition ' + name + r'\b.*?(?=^  (?:Definition|Example)|^End )',
            p256_source, re.MULTILINE | re.DOTALL,
        )
        code += definition.group() + '\n'
    code += 'End NativeP256Test.\n'
    create_names=['native_smoke_create_empty','native_smoke_create_deploy']
    exports=['NativeTxTest.'+n for n in names]+['NativeCreateTest.'+n for n in create_names]+['NativeEcrecoverTest.'+n for n in recovery_names]+['NativeP256Test.'+n for n in p256_names]
    code+='Extraction "@NATIVE_OUTPUT@/native_transaction_smoke.ml" '+ ' '.join(exports)+'.\n'
    (p/'NativeTransactionSmoke.v').write_text(code)
    main='''let report name passed =
      if passed then Printf.printf "PASS %s\\n%!" name
      else (Printf.eprintf "FAIL %s\\n%!" name; exit 1)

    let () =
    '''
    main+=';\n'.join(f'  report "{name}" Native_transaction_smoke.{mod}.{name}' for mod,name in [('NativeTxTest',n) for n in names]+[('NativeCreateTest',n) for n in create_names]+[('NativeEcrecoverTest',n) for n in recovery_names]+[('NativeP256Test',n) for n in p256_names])+'\n'
    (p/'native_transaction_main.ml').write_text(main)


def generate_authorization_smoke(output):
    names = [f"recover_pinned_authority_{i}" for i in range(3)]
    code = """From Stdlib Require Import Extraction ExtrOcamlBasic.
Require Import RocqOfRust.alloy_eip7702.tests.auth_list.
Extraction Language OCaml.
"""
    code += 'Extraction "@NATIVE_OUTPUT@/native_authorization_smoke.ml" '
    code += " ".join("auth_list.Test." + name for name in names) + ".\n"
    (output / "NativeAuthorizationSmoke.v").write_text(code)
    main = """let report name passed =
  if passed then Printf.printf "PASS %s\\n%!" name
  else (Printf.eprintf "FAIL %s\\n%!" name; exit 1)

let () =
"""
    main += ";\n".join(
        f'  report "{name}" Native_authorization_smoke.Test.{name}'
        for name in names
    ) + "\n"
    (output / "native_authorization_main.ml").write_text(main)


def generate(root, output, templates, numeric_backend="inductive"):
    output.mkdir(parents=True, exist_ok=True)
    for name in ["ContextLoad.v.in", "NativeNumericSmoke.v.in", "native_numeric_main.ml.in"]:
        source = templates/name
        (output/source.name.removesuffix(".in")).write_text(source.read_text())
    generate_context(root, output)
    generate_context_handlers(root, output)
    generate_context_runtime(root, output)
    generate_context_transactions(root, output)
    generate_transaction_smoke(root, output)
    generate_authorization_smoke(output)
    for source in output.glob("*.v"):
        code = source.read_text().replace("@NATIVE_OUTPUT@", output.as_posix())
        if numeric_backend == "zarith" or source.name in {"NativeAuthorizationSmoke.v", "NativeNumericSmoke.v"}:
            # Only the extracted representation and arithmetic primitives change.
            # The proved canonical specialization above is left intact.
            code = """From Stdlib Require Import ZArith ExtrOcamlZBigInt.
Extract Constant Z.shiftl => "Native_numeric_shifts.shiftl".
Extract Constant Z.shiftr => "Native_numeric_shifts.shiftr".
Extract Constant N.shiftl => "Native_numeric_shifts.shiftl_nonnegative".
Extract Constant N.shiftr => "Native_numeric_shifts.shiftr_nonnegative".
Extract Constant Z.pow => "Native_numeric_shifts.pow".
Extract Constant Z.land => "Z.logand".
Extract Constant Z.lor => "Z.logor".
Extract Constant Z.lxor => "Z.logxor".
Extract Constant Z.lnot => "Z.lognot".
""" + code
        source.write_text(code)
