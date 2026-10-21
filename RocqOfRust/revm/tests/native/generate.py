from pathlib import Path
import re

def generate_callhelpers(root, output):
    p = output
    prototype = output
    head = (output/'normalization_imports.v').read_text()
    head += 'From Stdlib Require Import FunctionalExtensionality.\nRequire Import OwnedAccountLoad.\n'
    black = (output/'normalization_keep.txt').read_text().strip()
    header_black = black
    code = head + f'''Definition native_load :=
     Eval cbv beta iota zeta delta - [{black}]
     in native_load_owned.
    Definition raw_load := account_load.load_account_delegated (H := StatefulHost.t) (H_types := StatefulHost.host_types).
    Lemma native_load_fn_eq : native_load = raw_load.
    Proof.
     repeat (apply functional_extensionality; intro).
     apply native_load_owned_eq.
    Qed.
    Definition raw_memranges := get_memory_input_and_out_ranges (WIRE := WIRE) (IInterpreterTypes := InterpreterTypes.I).
    Definition native_memranges :=
     Eval lazy beta iota delta - [{black}]
     in raw_memranges.
    Definition raw_accgas := load_acc_and_calc_gas (WIRE := WIRE) (H := StatefulHost.t) (H_types := StatefulHost.host_types) (IInterpreterTypes := InterpreterTypes.I).
    Definition raw_native_accgas : ltac:(let typ := type of raw_accgas in exact typ).
    Proof.
     let body := eval cbv beta iota zeta delta [raw_accgas load_acc_and_calc_gas] in raw_accgas in
     lazymatch body with
     | context C [@account_load.load_account_delegated _ _ _ _ _] =>
       let body := context C [native_load] in exact body
     end.
    Defined.
    Definition native_accgas :=
     Eval lazy beta iota delta - [native_load {black}]
     in raw_native_accgas.
    Lemma native_accgas_fn_eq : native_accgas = raw_accgas.
    Proof.
     change (raw_native_accgas = raw_accgas).
     unfold raw_native_accgas.
     rewrite native_load_fn_eq.
     reflexivity.
    Qed.
    '''
    for n,fn in [(241,'call'),(242,'call_code'),(244,'delegate_call'),(250,'static_call')]:
     area = 'RocqOfRust.revm.revm_interpreter.instructions.simulate.contract.' + fn
     code += 'Require Import ' + area + '.\n'
     code += f'''Definition raw_{n} : CallFrame.state -> CallFrame.state :=
     Eval cbv beta iota zeta delta [InterpreterDispatch.stateful InterpreterDispatch.simple Z.eqb Pos.eqb Z.leb Z.compare Pos.compare Integer.value andb]
     in InterpreterDispatch.stateful (H_types := StatefulHost.host_types) (IInterpreterTypes := InterpreterTypes.I) ({n} : u8).
    Definition raw_native_op_{n} : CallFrame.state -> CallFrame.state.
    Proof.
     let body := eval cbv beta iota zeta delta [raw_{n} {fn}] in raw_{n} in
     lazymatch body with
     | context C [@get_memory_input_and_out_ranges _ _ _ _ _] =>
       let body := context C [native_memranges] in
       lazymatch body with
       | context D [@load_acc_and_calc_gas _ _ _ _ _ _ _ _ _ _] =>
         let body := context D [native_accgas] in exact body
       end
     end.
    Defined.
    Definition op_{n} :=
     Eval lazy beta iota delta - [native_memranges native_accgas {black}]
     in raw_native_op_{n}.
    Lemma op_{n}_eq (state : CallFrame.state) :
     op_{n} state = InterpreterDispatch.stateful (H_types := StatefulHost.host_types) (IInterpreterTypes := InterpreterTypes.I) ({n} : u8) state.
    Proof.
     change (raw_native_op_{n} state = raw_{n} state).
     unfold raw_native_op_{n}.
     rewrite native_accgas_fn_eq.
     reflexivity.
    Qed.
    '''
    code += 'Set Extraction KeepSingleton.\nExtraction Language OCaml.\nExtraction "@NATIVE_OUTPUT@/callhelpers.ml" ' + ' '.join(f'op_{n}' for n in [241,242,244,250]) + '.\n'
    (output/'CallHelpers.v').write_text(code)


def generate_owned_host(root, output):
    p = output
    prototype = output
    names = ['balance','extcodesize','extcodecopy','extcodehash']
    sources = {n:(root/f'revm/revm_interpreter/instructions/simulate/host/{n}.v').read_text() for n in names}
    imports = (prototype/'normalization_imports.v').read_text().splitlines()+['From Stdlib Require Import List ZArith FunctionalExtensionality Extraction ExtrOcamlBasic ExtrOcamlString.', 'Require Import CallHelpers.', 'Require Import RocqOfRust.revm.revm_interpreter.tests.call_frame.']
    for name,source in sources.items():
     for line in source[:source.index('Definition '+name)].splitlines():
      if line.startswith('Require Import '):imports.append(line.replace('Require Import ', 'Require Import RocqOfRust.'))
     imports.append('Require Import RocqOfRust.revm.revm_interpreter.instructions.simulate.host.'+name+'.')
    imports.append('Require Import RocqOfRust.alloy_primitives.bits.links.address.')
    imports=list(dict.fromkeys(imports))
    code='\n'.join(imports)+'''\nImport ListNotations.
    Open Scope Z_scope.
    Definition native_load_then {K : Set} (host : StatefulHost.t) (address : Address.t)
        (load_code skip_cold : bool)
        (k : Result.t AccountInfoLoad.t LoadError.t -> StatefulHost.t -> K) : K :=
     if skip_cold && negb (StatefulHost.account_is_warm host address.(Address.value)) then
       k (Result.Err LoadError.ColdLoadSkipped) host
     else k (Result.Ok (StatefulHost.account_info_load host address load_code))
       (StatefulHost.warm_account host address.(Address.value)).
    Lemma native_load_then_eq {K : Set} (host : StatefulHost.t) (address : Address.t)
        (load_code skip_cold : bool)
        (k : Result.t AccountInfoLoad.t LoadError.t -> StatefulHost.t -> K) :
     native_load_then host address load_code skip_cold k =
     let '(result,host) := StatefulHost.load_account_info_skip_cold_load host address load_code skip_cold in
     k result host.
    Proof.
     unfold native_load_then, StatefulHost.load_account_info_skip_cold_load.
     destruct (skip_cold && negb (StatefulHost.account_is_warm host address.(Address.value))); reflexivity.
    Qed.
    '''
    code += '''
    Definition raw_load_then {K : Set} (host : StatefulHost.t) (address : Address.t)
        (load_code skip_cold : bool)
        (k : Result.t AccountInfoLoad.t LoadError.t -> StatefulHost.t -> K) : K :=
     let '(result,host) := StatefulHost.load_account_info_skip_cold_load host address load_code skip_cold in k result host.
    Lemma native_load_then_fn_eq {K : Set} : @native_load_then K = @raw_load_then K.
    Proof.
     repeat (apply functional_extensionality; intro).
     apply native_load_then_eq.
    Qed.
    '''
    black=(prototype/'normalization_keep.txt').read_text().strip()+' StatefulHost.selfdestruct'
    for name,source in sources.items():
     begin=source.index('Definition '+name)
     body_begin=source.index(':=',begin)+2
     body_end=re.search(r'\n(?:Lemma|Ltac|Module) ',source[body_begin:]).start()+body_begin
     body=source[body_begin:body_end].strip()[:-1]
     pattern = r"let '\(account_result, host\) :=\s*IHost\.\(Host\.load_account_info_skip_cold_load\) (\w+) (\w+) (true|false) (\w+) in\s*match account_result with"
     for m in reversed(list(re.finditer(pattern,body))):
      match_start=body.index('match account_result with',m.start())
      depth=0;end=None
      for token in re.finditer(r'\b(match|end)\b',body[match_start:]):
       depth += 1 if token[1]=='match' else -1
       if depth==0:
        end=match_start+token.end();break
      assert end is not None
      match_body=body[match_start:end]
      args=' '.join(m.groups())
      replacement=f'native_load_then {args} (fun account_result host =>\n{match_body})'
      body=body[:m.start()]+replacement+body[end:]
     code+=f'''Definition owned_{name} (interpreter : CallFrame.machine) (host : StatefulHost.t) :
     CallFrame.machine * StatefulHost.t :=
     let IInterpreterTypes := InterpreterTypes.I in
     let IHost := StatefulHost.HostForRevmHost in
     {body}.
    Lemma owned_{name}_eq (interpreter : CallFrame.machine) (host : StatefulHost.t) :
     owned_{name} interpreter host = {name} (H_types := StatefulHost.host_types)
       (IInterpreterTypes := InterpreterTypes.I) interpreter host.
    Proof.
     unfold owned_{name}, {name}.
     rewrite !native_load_then_fn_eq.
     reflexivity.
    Qed.
    Definition native_{name} :=
     Eval cbv beta iota zeta delta - [{black}]
     in owned_{name}.
    Lemma native_{name}_fn_eq : native_{name} =
     {name} (WIRE := WIRE) (H := StatefulHost.t) (H_types := StatefulHost.host_types) (IInterpreterTypes := InterpreterTypes.I).
    Proof.
     repeat (apply functional_extensionality; intro).
     apply owned_{name}_eq.
    Qed.
    '''
    code+='Set Extraction KeepSingleton.\nExtraction Language OCaml.\nExtraction "@NATIVE_OUTPUT@/owned_host.ml" '+' '.join('native_'+n for n in names)+'.\n'
    (prototype/'OwnedHost.v').write_text(code)


def generate_handlers(root, output):
    p = output
    prototype = output
    source = (root / 'revm/revm_interpreter/simulate/dispatch.v').read_text()
    simple = source[source.index('  Definition simple'):source.index('  Lemma simple_stop')]
    stateful = source[source.index('  Definition stateful'):source.index('  Definition step_result_stateful')]
    simple_codes = list(map(int, re.findall(r'Z.eqb opcode\.\(Integer.value\) (\d+)', simple)))
    stateful_codes = list(map(int, re.findall(r'Z.eqb opcode\.\(Integer.value\) (\d+)', stateful)))
    codes = list(dict.fromkeys(stateful_codes + simple_codes))
    black = (prototype / 'normalization_keep.txt').read_text().strip() + ' StatefulHost.selfdestruct'
    head = (prototype / 'normalization_imports.v').read_text()
    head += '''Require Import CallHelpers.
    Require Import OwnedHost.
    Require Import RocqOfRust.revm.revm_interpreter.instructions.simulate.stack.push.
    Require Import RocqOfRust.revm.revm_interpreter.instructions.simulate.stack.dup.
    Require Import RocqOfRust.revm.revm_interpreter.instructions.simulate.stack.swap.
    '''
    out = head
    owned_functions={49:'balance',59:'extcodesize',60:'extcodecopy',63:'extcodehash'}
    for n, name in owned_functions.items():
     out += f'''Definition raw_{n} : CallFrame.state -> CallFrame.state :=
     Eval cbv beta iota zeta delta [InterpreterDispatch.stateful InterpreterDispatch.simple Z.eqb Pos.eqb Z.leb Z.compare Pos.compare Integer.value andb]
     in InterpreterDispatch.stateful (H_types := StatefulHost.host_types) (IInterpreterTypes := InterpreterTypes.I) ({n} : u8).
    Definition raw_native_op_{n} : CallFrame.state -> CallFrame.state.
    Proof.
     let body := eval cbv beta iota zeta delta [raw_{n}] in raw_{n} in
     lazymatch body with
     | context C [@RocqOfRust.revm.revm_interpreter.instructions.simulate.host.{name}.{name} _ _ _ _ _ _ _ _ _ _] =>
       let body := context C [native_{name}] in exact body
     end.
    Defined.
    Definition op_{n} :=
     Eval cbv beta iota zeta delta - [native_{name} {black}]
     in raw_native_op_{n}.
    Lemma op_{n}_eq (state : CallFrame.state) :
     op_{n} state = InterpreterDispatch.stateful (H_types := StatefulHost.host_types) (IInterpreterTypes := InterpreterTypes.I) ({n} : u8) state.
    Proof.
     change (raw_native_op_{n} state = raw_{n} state).
     unfold raw_native_op_{n}.
     rewrite native_{name}_fn_eq.
     reflexivity.
    Qed.
    '''
    for n in codes + [12]:
     if n in [241,242,244,250] or n in owned_functions:
      continue
     out += f'''Definition raw_{n} : CallFrame.state -> CallFrame.state :=
     Eval cbv beta iota zeta delta [InterpreterDispatch.stateful InterpreterDispatch.simple Z.eqb Pos.eqb Z.leb Z.compare Pos.compare Integer.value andb]
     in InterpreterDispatch.stateful (H_types := StatefulHost.host_types) (IInterpreterTypes := InterpreterTypes.I) ({n} : u8).
    Definition op_{n} : CallFrame.state -> CallFrame.state :=
     Eval cbv beta iota zeta delta - [{black}]
     in raw_{n}.
    Lemma op_{n}_eq (state : CallFrame.state) :
     op_{n} state = InterpreterDispatch.stateful (H_types := StatefulHost.host_types) (IInterpreterTypes := InterpreterTypes.I) ({n} : u8) state.
    Proof. reflexivity. Qed.
    '''
    for name in ['push','dup','swap']:
     out += f'''Definition raw_{name} (n : usize) : CallFrame.state -> CallFrame.state :=
     InstructionContext.map_interpreter ({name} (IInterpreterTypes := InterpreterTypes.I) n).
    Definition op_{name} :=
     Eval cbv beta iota zeta delta - [{black}]
     in raw_{name}.
    '''
    out += '''Definition native_dispatch (opcode : u8) (state : CallFrame.state) : CallFrame.state :=
    '''
    for n in codes:
     out += f' if Z.eqb opcode.(Integer.value) {n} then op_{n} state else\n'
    for low,high,name,offset in [(96,127,'push',95),(128,143,'dup',127),(144,159,'swap',143)]:
     out += f' if ({low} <=? opcode.(Integer.value)) && (opcode.(Integer.value) <=? {high}) then\n  op_{name} {{| Integer.value := opcode.(Integer.value) - {offset} |}} state else\n'
    out += ''' op_12 state.
    Lemma native_dispatch_eq (opcode : u8) (state : CallFrame.state) :
     native_dispatch opcode state = InterpreterDispatch.stateful
       (H_types := StatefulHost.host_types) (IInterpreterTypes := InterpreterTypes.I) opcode state.
    Proof.
     destruct opcode as [opcode].
     unfold native_dispatch, InterpreterDispatch.stateful, InterpreterDispatch.simple.
     cbv beta iota zeta delta [Integer.value].
    '''
    for n in codes:
     out += f''' destruct (Z.eqb opcode {n}) eqn:H_{n}.
     {{ apply Z.eqb_eq in H_{n}. subst opcode. apply op_{n}_eq. }}
    '''
    for low,high,name in [(96,127,'push'),(128,143,'dup'),(144,159,'swap')]:
     out += f''' destruct (({low} <=? opcode) && (opcode <=? {high})).
     {{ reflexivity. }}
    '''
    out += ''' apply op_12_eq.
    Qed.
    Set Extraction KeepSingleton.
    Extraction Language OCaml.
    Extraction "@NATIVE_OUTPUT@/handlers.ml" native_dispatch.
    '''
    (prototype / 'Handlers.v').write_text(out)


def generate_framehelpers(root, output):
    p = output
    prototype = output
    r=root/'revm/revm_interpreter/tests'
    imports=(p/'frame_imports.v').read_text()
    code=imports+'\n'
    fs=re.findall(r'^  (?:Definition|Fixpoint) (\w+)',(r/'stateful_host.v').read_text(),re.M)
    fs=[f for f in fs if f not in ['identity_ref','transaction_types','host_types']]
    keep=' '.join('StatefulHost.'+f for f in fs)+' '+(p/'normalization_keep.txt').read_text().strip()
    keep+=' Memory.take_pad Memory.slice Memory.extend_to Memory.set_bytes_at Memory.set Memory.set_data Memory.copy Memory.resize Memory.size'
    keep+=' Impl_Gas.new Impl_Gas.erase_cost Impl_Gas.record_refund Impl_Gas.record_cost CreateAddress.create CreateAddress.create2'
    keep+=' RocqOfRust.revm.revm_precompile.simulate.sha256.Sha256.hash RocqOfRust.revm.revm_precompile.simulate.ripemd160.Ripemd160.hash RocqOfRust.revm.revm_precompile.simulate.modexp.Modexp.run_osaka RocqOfRust.revm.revm_precompile.simulate.modexp.Modexp.run_berlin'
    keep += ' RocqOfRust.revm.revm_precompile.simulate.modexp.Modexp.run_byzantium RocqOfRust.revm.revm_precompile.simulate.blake2.Blake2.run'
    keep += ' RocqOfRust.revm.revm_precompile.simulate.bn254.Bn254.run_add RocqOfRust.revm.revm_precompile.simulate.bn254.Bn254.run_mul'
    secp = 'RocqOfRust.revm.revm_precompile.simulate.secp256k1.Secp256k1.'
    keep += ' ' + ' '.join(secp + name for name in [
        'output', 'recover', 'recover_public_key', 'address', 'scalar_valid',
        'Field.add', 'Field.sub', 'Field.mul', 'Field.square', 'Field.negate', 'Field.inverse',
        'Point.is_infinity', 'Point.of_affine', 'Point.to_affine', 'Point.on_curve',
        'Point.double', 'Point.add', 'Point.mul_positive', 'Point.mul',
    ])
    keep += ' RocqOfRust.revm.revm_precompile.simulate.modexp.Modexp.pow_mod'
    keep += ' RocqOfRust.revm.revm_precompile.simulate.secp256r1.secp256r1.p256_verify_inner'
    keep += ' RocqOfRust.revm.revm_precompile.simulate.bls12_381.g1_add.g1_add.g1_add'
    keep += ' RocqOfRust.revm.revm_precompile.simulate.bls12_381.g1_msm.g1_msm.g1_msm'
    keep += ' RocqOfRust.revm.revm_precompile.simulate.bls12_381.g2_add.g2_add.g2_add'
    keep += ' RocqOfRust.revm.revm_precompile.simulate.bls12_381.g2_msm.g2_msm.g2_msm'
    keep += ' RocqOfRust.revm.revm_precompile.simulate.bls12_381.map_fp_to_g1.map_fp_to_g1.map_fp_to_g1'
    keep += ' RocqOfRust.revm.revm_precompile.simulate.bls12_381.map_fp2_to_g2.map_fp2_to_g2.map_fp2_to_g2'
    keep += ' RocqOfRust.revm.revm_precompile.simulate.bls12_381.pairing.pairing.pairing'
    items=['make_interpreter_with_bytecode','interpreter_with_spec_id','CallFrame.result','CallFrame.resume','CallFrame.child','CallFrame.transfer','CreateFrame.result','CreateFrame.child','CreateFrame.prepare','CreateFrame.resume','CreateFrame.finish','PrecompileFrame.run']
    previous=[]
    for original in items:
     native='native_'+original.replace('.','_')
     raw='raw_'+original.replace('.','_')
     code+=f'Definition {raw} := ltac:(\n let body := eval cbv delta [{original}] in {original} in\n'
     for old,new in previous:
      code+=f''' let rec subst_term body :=
      lazymatch body with
      | context C [{old}] => let body := context C [{new}] in subst_term body
      | _ => constr:(body)
      end in
     let body := subst_term body in
    '''
     code+=' exact body).\n'
     code+=f'Definition {native} := Eval lazy beta iota delta - [{keep} '+ ' '.join(n for _,n in previous)+f'] in {raw}.\n'
     code+=f'Lemma {native}_fn_eq : {native} = {original}.\nProof.\n change ({raw} = {original}).\n unfold {raw}.\n'
     if previous:code+=''.join(' try rewrite '+n+'_fn_eq.\n' for _,n in previous)
     code+=' reflexivity.\nQed.\n'
     previous.append((original,native))
    code+='Set Extraction KeepSingleton.\nExtraction Language OCaml.\nExtraction "@NATIVE_OUTPUT@/framehelpers.ml" '+' '.join(n for _,n in previous)+'.\n'
    (p/'FrameHelpers.v').write_text(code)
    (p/'frame_keep.txt').write_text(keep)
    (p/'frame_items.txt').write_text('\n'.join(old+' '+new for old,new in previous))


def generate_runtime(root, output):
    p = output
    prototype = output
    imports=(p/'runtime_imports.v').read_text()
    items=[l.split() for l in (p/'frame_items.txt').read_text().splitlines()]
    keep=(p/'frame_keep.txt').read_text()+' '+' '.join(new for _,new in items)+' native_step'
    code=imports+'''Definition raw_native_execute_with_finalization := ltac:(
     let body := eval cbv beta delta [CallRunner.execute_with_step]
      in (CallRunner.execute_with_step native_step) in
    '''
    for original,native in items:
     code+=f''' let rec subst_term body :=
      lazymatch body with
      | context C [{original}] => let body := context C [{native}] in subst_term body
      | _ => constr:(body)
      end in
     let body := subst_term body in
    '''
    code+=' exact body).\n'
    code+=f'Definition native_execute_with_finalization := Eval lazy beta iota delta - [{keep}] in raw_native_execute_with_finalization.\n'
    code+='''Lemma native_execute_with_finalization_eq :
     native_execute_with_finalization = CallRunner.execute_with_finalization.
    Proof.
     change (raw_native_execute_with_finalization = CallRunner.execute_with_finalization).
     unfold raw_native_execute_with_finalization, CallRunner.execute_with_finalization.
    '''
    code+=''.join(' try rewrite '+n+'_fn_eq.\n' for _,n in items)
    code+=' rewrite native_step_fn_eq. reflexivity.\nQed.\n'
    smoke=(p/'runtime_smoke.v').read_text()
    code+=smoke
    code+=f'Definition native_smoke := Eval lazy beta iota delta - [{keep} native_execute_with_finalization] in raw_native_smoke.\n'
    code+=(p/'runtime_smoke_tests.v').read_text()
    (p/'NativeRuntime.v').write_text(code)


def generate_transactions(root, output):
    p = output
    prototype = output
    source=(root/'revm/revm_handler/simulate/legacy_call.v').read_text()
    imports=(p/'FrameHelpers.v').read_text().split('Definition raw_make')[0]
    for line in source.split('Module LegacyCall.')[0].splitlines():
     if line.startswith('Require Import '):
      imports+=line.replace('Require Import ','Require Import RocqOfRust.')+'\n'
    imports+='Require Import RocqOfRust.revm.revm_handler.simulate.legacy_call.\nRequire Import RocqOfRust.revm.revm_handler.simulate.eest_transaction.\nRequire Import RocqOfRust.revm.revm_handler.simulate.transaction_auth.\nRequire Import RocqOfRust.revm.revm_handler.simulate.transaction_validation.\nRequire Import RocqOfRust.revm.revm_handler.simulate.ethereum_commitment.\nRequire Import NativeRuntime.\nRequire Import FrameHelpers.\n'
    keep=(p/'frame_keep.txt').read_text()+' native_execute_with_finalization'
    items=[l.split() for l in (p/'frame_items.txt').read_text().splitlines()]
    keep+=' '+' '.join(new for _,new in items)
    accounting=(root/'revm/revm_handler/simulate/transaction_accounting.v').read_text()
    keep+=' '+' '.join('TransactionAccounting.'+name for name in re.findall(r'^  (?:Definition|Fixpoint) (\w+)',accounting,re.M))
    # Keep authorization processing shared instead of unfolding its signature
    # recovery and journal implementation into the transaction specialization.
    keep += ' pre_execution.apply_eip7702_auth_list handler.first_frame_input'
    keep += ' post_execution.reimburse_caller post_execution.reward_beneficiary'
    keep += ' Impl_AuthorizationTr_for_SignedAuthorization.methods'
    keep += ' RocqOfRust.alloy_eip7702.simulate.auth_list.SignedAuthorization.recover_authority RocqOfRust.alloy_eip7702.simulate.auth_list.Authorization.signature_hash'
    keep+=' '+ ' '.join('LegacyCall.'+name for name in re.findall(r'^  (?:Definition|Fixpoint) (\w+)',source,re.M) if name not in ['execute_with_runner','execute','run_with_runner','run'])
    code=imports+'''Definition raw_native_transaction_execute := ltac:(
     let body := eval cbv beta delta [LegacyCall.execute_with_runner]
      in (LegacyCall.execute_with_runner native_execute_with_finalization) in
    '''
    for original,native in items:
     code+=f''' let rec subst_term body :=
      lazymatch body with
      | context C [{original}] => let body := context C [{native}] in subst_term body
      | _ => constr:(body)
      end in
     let body := subst_term body in
    '''
    code+=' exact body).\n'
    code+=f'Definition native_transaction_execute := Eval lazy beta iota delta - [{keep}] in raw_native_transaction_execute.\n'
    code+='''Lemma native_transaction_execute_fn_eq : native_transaction_execute =
     LegacyCall.execute_with_runner native_execute_with_finalization.
    Proof.
     change (raw_native_transaction_execute = LegacyCall.execute_with_runner native_execute_with_finalization).
     unfold raw_native_transaction_execute.
    '''
    code+=''.join(' try rewrite '+n+'_fn_eq.\n' for _,n in items)
    code+=' reflexivity.\nQed.\n'
    code+='''Definition raw_native_transaction_run := ltac:(
     let body := eval cbv beta delta [LegacyCall.run_with_runner]
      in (LegacyCall.run_with_runner native_execute_with_finalization) in
     let rec subst_term body :=
      lazymatch body with
      | context C [LegacyCall.execute_with_runner native_execute_with_finalization] =>
        let body := context C [native_transaction_execute] in subst_term body
      | _ => constr:(body)
      end in
     let body := subst_term body in exact body).
    '''
    code+=f'Definition native_transaction_run := Eval lazy beta iota delta - [{keep} native_transaction_execute] in raw_native_transaction_run.\n'
    code+='''Lemma native_transaction_run_eq : native_transaction_run = LegacyCall.run.
    Proof.
     change (raw_native_transaction_run = LegacyCall.run).
     unfold raw_native_transaction_run, LegacyCall.run.
     rewrite !native_transaction_execute_fn_eq.
     rewrite native_execute_with_finalization_eq.
     reflexivity.
    Qed.
    Definition native_eest_transaction_run := EestTransaction.run_with native_transaction_run.
    Lemma native_eest_transaction_run_eq : native_eest_transaction_run = EestTransaction.run.
    Proof. unfold native_eest_transaction_run, EestTransaction.run, EestTransaction.run_with.
      rewrite native_transaction_run_eq. reflexivity. Qed.
    Set Extraction KeepSingleton.
    Extraction Language OCaml.
    Extraction "@NATIVE_OUTPUT@/native_transactions.ml" native_transaction_run native_eest_transaction_run
      TransactionAuth.authenticate TransactionAuth.authenticate_for_spec
      TransactionValidation.validate EthereumCommitment.state_root EthereumCommitment.logs_hash.
    '''
    (p/'NativeTransactions.v').write_text(code)


def generate_transaction_smoke(root, output):
    p = output
    prototype = output
    s=(root/'revm/revm_handler/tests/legacy_call.v').read_text()
    base=s[s.index('  Definition tx'):s.index('  Lemma stop_applies')]
    fees=s[s.index('  Definition access_list_tx'):s.index('  Lemma access_list_stop')]
    blob=s[s.index('  Definition blob_hash'):s.index('  Lemma blob_stop')]
    body=(base+fees+blob)
    code=(p/'NativeTransactions.v').read_text().split('Definition raw_native_transaction_execute')[0]+'Require Import NativeTransactions.\nRequire Import RocqOfRust.alloy_primitives.utils.simulate.keccak256.\nRequire Import RocqOfRust.revm.revm_precompile.simulate.modexp.\nModule NativeTxTest.\n'+body
    code+='''
     Definition check_observation (status : InstructionResult.t)
         (gas nonce sender target coinbase slot : Z) (result : LegacyCall.Result.t) : bool :=
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
     | LegacyCall.Result.Rejected LegacyCall.Rejection.{reason} => true
     | _ => false end.
    '''
    create_source=(root/'revm/revm_handler/tests/legacy_create.v').read_text()
    create_body=create_source[create_source.index('  Definition tx'):create_source.index('  Lemma stop_creates')]
    create_body=create_body.replace('LegacyCall.run','native_transaction_run')
    code+='End NativeTxTest.\nModule NativeCreateTest.\n'+create_body
    code+='''Definition check_creation (deploy : bool) (gas sender coinbase : Z) (result : LegacyCall.Result.t) :=
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
      (NativeTxTest.tx <| TransactionAccounting.Transaction.target := Some 1 |>
        <| TransactionAccounting.Transaction.data := data |>) (NativeTxTest.input []).
    Definition check_precompile (expected : list Z) (used sender_balance reward : Z)
        (result : LegacyCall.Result.t) : bool :=
      match result with
      | LegacyCall.Result.Completed output =>
        let gas := output.(LegacyCall.Output.gas) in
        let sender := LegacyCall.account_at 100 output.(LegacyCall.Output.accounts) in
        let target := LegacyCall.account_at 1 output.(LegacyCall.Output.accounts) in
        let coinbase := LegacyCall.account_at 99 output.(LegacyCall.Output.accounts) in
        let returned := match output.(LegacyCall.Output.status) with
          | InstructionResult.Return => true | _ => false end in
        returned && bytes_eq output.(LegacyCall.Output.data) expected &&
          (gas.(TransactionAccounting.Settlement.gas_used) =? used) &&
          (gas.(TransactionAccounting.Settlement.gas_remaining) =? 50000 - used) &&
          (gas.(TransactionAccounting.Settlement.gas_refunded) =? 0) &&
          (gas.(TransactionAccounting.Settlement.caller_reimbursement) =? (50000 - used) * 10) &&
          (gas.(TransactionAccounting.Settlement.beneficiary_reward) =? reward) &&
          (gas.(TransactionAccounting.Settlement.base_fee_burn) =? used * 4) &&
          (gas.(TransactionAccounting.Settlement.blob_fee_burn) =? 0) &&
          (sender.(StatefulHost.Account.nonce) =? 1) &&
          (sender.(StatefulHost.Account.balance) =? sender_balance) &&
          (target.(StatefulHost.Account.balance) =? 7) &&
          (coinbase.(StatefulHost.Account.balance) =? reward)
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
    for source in templates.iterdir():
        if source.is_file():
            (output/source.name.removesuffix(".in")).write_text(source.read_text())
    generate_callhelpers(root, output)
    generate_owned_host(root, output)
    generate_handlers(root, output)
    generate_framehelpers(root, output)
    generate_runtime(root, output)
    generate_transactions(root, output)
    generate_transaction_smoke(root, output)
    generate_authorization_smoke(output)
    for source in output.glob("*.v"):
        code = source.read_text().replace("@NATIVE_OUTPUT@", output.as_posix())
        if numeric_backend == "zarith" or source.name == "NativeAuthorizationSmoke.v":
            # Only the extracted representation and arithmetic primitives change.
            # The proved canonical specialization above is left intact.
            code = """From Stdlib Require Import ZArith ExtrOcamlZBigInt.
Extract Constant Z.shiftl => "Native_numeric_shifts.shiftl".
Extract Constant Z.shiftr => "Native_numeric_shifts.shiftr".
Extract Constant N.shiftl => "Native_numeric_shifts.shiftl_nonnegative".
Extract Constant N.shiftr => "Native_numeric_shifts.shiftr_nonnegative".
Extract Constant Z.land => "Z.logand".
Extract Constant Z.lor => "Z.logor".
Extract Constant Z.lxor => "Z.logxor".
Extract Constant Z.lnot => "Z.lognot".
""" + code
        source.write_text(code)
