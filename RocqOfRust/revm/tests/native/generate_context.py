"""Specialize the typed Context interpreter, checking each substitution in Rocq."""
import re


def definition_body(source, name):
    start = source.index('Definition ' + name)
    start = source.index(':=', start) + 2
    rest = source[start:]
    end = re.search(r'\n\s*(?:Lemma|Example|Ltac|Module|End|Definition|Fixpoint)\b', rest)
    return rest[:end.start() if end else len(rest)].strip().removesuffix('.')


def owned_loads(body):
    pattern = (r"let '\((\w+), host\) :=\s*"
               r"IHost\.\(Host\.load_account_info_skip_cold_load\)\s*"
               r"(\w+) (\w+) (true|false) (\w+) in\s*match \1 with")
    matches = list(re.finditer(pattern, body))
    # Work from the inside out, preserving the canonical continuation verbatim.
    for m in reversed(matches):
        match_start = body.index('match ' + m[1] + ' with', m.start())
        depth = 0
        for token in re.finditer(r'\b(match|end)\b', body[match_start:]):
            depth += 1 if token[1] == 'match' else -1
            if depth == 0:
                end = match_start + token.end()
                break
        else:
            raise ValueError('Unbalanced canonical account-load match')
        continuation = body[match_start:end]
        args = ' '.join(m.groups()[1:])
        body = body[:m.start()] + f'context_load_then {args} (fun {m[1]} host =>\n{continuation})' + body[end:]
    if not matches:
        raise ValueError('Expected a canonical account load')
    return body


def generate_context(root, output):
    imports = (root/'revm/tests/native/templates/normalization_imports.v.in').read_text()
    imports += '''
From Stdlib Require Import FunctionalExtensionality.
Require Import ContextLoad.
Require Import RocqOfRust.revm.revm_handler.simulate.eest_context.
Require Import RocqOfRust.revm.revm_handler.simulate.eest_types.
Require Import RocqOfRust.revm.revm_context.simulate.context.
Require Import RocqOfRust.revm.revm_context.simulate.host.
Require Import RocqOfRust.revm.revm_state.simulate.lib.
Require Import RocqOfRust.revm.revm_context.simulate.journal.
Require Import RocqOfRust.revm.revm_context.journal.simulate.inner.
Require Import RocqOfRust.revm.revm_context_interface.simulate.host_runtime.
Require Import RocqOfRust.revm.revm_interpreter.simulate.runtime.
Require Import RocqOfRust.revm.revm_interpreter.instructions.simulate.runtime_host.
Require Import RocqOfRust.revm.revm_interpreter.links.interpreter.
Require Import RocqOfRust.alloy_primitives.bits.links.address.
'''
    names = ['balance', 'extcodesize', 'extcodecopy', 'extcodehash', 'call', 'call_code', 'delegate_call', 'static_call']
    sources = {}
    for name in names:
        area = 'contract' if name in names[4:] else 'host'
        source = (root/f'revm/revm_interpreter/instructions/simulate/{area}/{name}.v').read_text()
        sources[name] = source
        imports += '\n'.join(line.replace('Require Import ', 'Require Import RocqOfRust.')
                             for line in source[:source.index('Definition '+name)].splitlines()
                             if line.startswith('Require Import ')) + '\n'
    imports += '''
Definition machine := Interpreter.t WIRE WIRE_types.
Definition ctx := Context.t EestTypes.Input.t unit.
'''
    keep = (root/'revm/tests/native/templates/normalization_keep.txt').read_text().strip()
    for path, module in [
        ('revm/revm_context/simulate/context.v', 'Impl_Host_for_Context'),
        ('revm/revm_context/simulate/host.v', 'ContextHost'),
        ('revm/revm_context/journal/simulate/inner.v', 'Impl_JournalInner'),
        ('revm/revm_context/simulate/journal.v', 'Impl_Journal'),
    ]:
        source = (root/path).read_text().split('Module '+module+'.')[1].split('End '+module+'.')[0]
        keep += ' '+' '.join(module+'.'+name for name in re.findall(r'^  (?:Definition|Fixpoint) (\w+)', source, re.M))
    keep += ' FixedBytes.to_Z FixedBytes.from_Z Impl_Account.state_clear_aware_is_empty EestContext.database'
    code = imports
    source = (root/'revm/revm_interpreter/instructions/contract/simulate/account_load.v').read_text()
    body = owned_loads(definition_body(source, 'load_account_delegated'))
    code += f'''Definition owned_account_load (host : ctx) (spec : SpecId.t) (remaining_gas : u64)
      (address : Address.t) (transfers_value create_empty_account : bool) := {body}.
'''
    source = (root/'revm/revm_interpreter/instructions/contract/simulate/call_helpers.v').read_text()
    body = definition_body(source, 'load_acc_and_calc_gas').replace('account_load.load_account_delegated', 'owned_account_load').replace('LoadAccAndCalcGasResult.', 'call_helpers.LoadAccAndCalcGasResult.')
    code += f'''Definition owned_accgas (interpreter : machine) (host : ctx) (to : Address.t)
      (transfers_value create_empty_account : bool) (stack_gas_limit : u64) :=
      let IInterpreterTypes := InterpreterTypes.I in {body}.
'''
    code += f"""
Definition native_account_load := Eval cbv beta iota zeta delta - [{keep}] in owned_account_load.
Definition native_memranges := Eval cbv beta iota zeta delta - [{keep}] in
  call_helpers.get_memory_input_and_out_ranges (WIRE := WIRE) (IInterpreterTypes := InterpreterTypes.I).
Definition raw_native_accgas := ltac:(
  let body := eval cbv beta delta [owned_accgas] in owned_accgas in
  lazymatch body with context C [owned_account_load] => let body := context C [native_account_load] in exact body end).
Definition native_accgas := Eval cbv beta iota zeta delta - [{keep} native_account_load] in raw_native_accgas.
"""
    keep += ' native_account_load native_accgas native_memranges'
    for name in names:
        body = definition_body(sources[name], name)
        if name in names[:4]:
            body = owned_loads(body)
        else:
            body = body.replace('call_helpers.load_acc_and_calc_gas', 'owned_accgas')
        body = body.replace('IHost.(Host.', 'ContextHost.methods.(HostRuntime.')
        code += f'''Definition owned_{name} (interpreter : machine) (host : ctx) : machine * ctx :=
      let IInterpreterTypes := InterpreterTypes.I in {body}.
Lemma owned_{name}_eq : owned_{name} = RuntimeInstructions.{name} (IInterpreterTypes := InterpreterTypes.I).
Proof.
  unfold owned_{name}, owned_accgas, owned_account_load.
  rewrite !context_load_then_fn_eq.
  reflexivity.
Qed.
Definition raw_native_{name} := ltac:(
  let body := eval cbv beta delta [owned_{name}] in owned_{name} in
  let rec replace_helpers body := lazymatch body with
  | context C [owned_accgas] => let body := context C [native_accgas] in replace_helpers body
  | context C [@call_helpers.get_memory_input_and_out_ranges _ _ _ _ _] =>
      let body := context C [native_memranges] in replace_helpers body
  | _ => body end in
  let body := replace_helpers body in exact body).
Definition native_{name} := Eval cbv beta iota zeta delta - [{keep}] in raw_native_{name}.
Lemma native_{name}_eq : native_{name} = RuntimeInstructions.{name} (IInterpreterTypes := InterpreterTypes.I).
Proof. exact owned_{name}_eq. Qed.
'''

    (output/'ContextOwned.v').write_text(code)
    (output/'context_keep.txt').write_text(keep)


def generate_context_handlers(root, output):
    source = (root/'revm/revm_interpreter/simulate/runtime.v').read_text()
    table = source[source.index('  Definition execute'):source.index('End RuntimeInstructionTable.')]
    codes = list(map(int, re.findall(r'if Z.eqb byte (\d+) then', table)))
    keep = (output/'context_keep.txt').read_text()
    owned = {49: 'balance', 59: 'extcodesize', 60: 'extcodecopy', 63: 'extcodehash',
             241: 'call', 242: 'call_code', 244: 'delegate_call', 250: 'static_call'}
    code = (output/'ContextOwned.v').read_text().split('Definition owned_account_load')[0]
    code += 'Require Import ContextOwned.\n'
    for name in ['push', 'dup', 'swap']:
        code += f'Require Import RocqOfRust.revm.revm_interpreter.instructions.simulate.stack.{name}.\n'
    for number in codes + [12]:
        code += f'''Definition raw_{number} : machine -> ctx -> machine * ctx :=
  Eval cbv beta iota zeta delta [RuntimeInstructionTable.execute Z.eqb Pos.eqb Z.leb Z.compare Pos.compare Integer.value andb]
  in RuntimeInstructionTable.execute (IInterpreterTypes := InterpreterTypes.I) ({number} : u8).
'''
        if number in owned:
            name = owned[number]
            code += f'''Definition op_{number} := native_{name}.
Lemma op_{number}_eq : op_{number} = raw_{number}.
Proof. exact native_{name}_eq. Qed.
'''
        else:
            code += f'''Definition op_{number} := Eval cbv beta iota zeta delta - [{keep}] in raw_{number}.
Lemma op_{number}_eq : op_{number} = raw_{number}.
Proof. reflexivity. Qed.
'''
    for name in ['push', 'dup', 'swap']:
        code += f'''Definition op_{name} (n : usize) : machine -> ctx -> machine * ctx :=
  Eval cbv beta iota zeta delta - [{keep}] in
  (fun interpreter host => ({name} (IInterpreterTypes := InterpreterTypes.I) n interpreter, host)).
'''
    code += 'Definition native_dispatch (opcode : u8) (interpreter : machine) (host : ctx) :=\n'
    for number in codes:
        code += f'  if Z.eqb opcode.(Integer.value) {number} then op_{number} interpreter host else\n'
    for low, high, name, offset in [(96, 127, 'push', 95), (128, 143, 'dup', 127), (144, 159, 'swap', 143)]:
        code += f'''  if Z.leb {low} opcode.(Integer.value) && Z.leb opcode.(Integer.value) {high} then
    op_{name} {{| Integer.value := opcode.(Integer.value) - {offset} |}} interpreter host else
'''
    code += '''  op_12 interpreter host.
Lemma native_dispatch_eq : native_dispatch =
  RuntimeInstructionTable.execute (WIRE := WIRE) (H := ctx) (IInterpreterTypes := InterpreterTypes.I).
Proof.
  apply functional_extensionality. intros [opcode].
  apply functional_extensionality. intro interpreter.
  apply functional_extensionality. intro host.
  unfold native_dispatch, RuntimeInstructionTable.execute.
  cbv beta iota zeta delta [Integer.value].
'''
    for number in codes:
        code += f'''  destruct (Z.eqb opcode {number}) eqn:case_{number}.
  {{ apply Z.eqb_eq in case_{number}. subst opcode. rewrite op_{number}_eq. reflexivity. }}
'''
    for low, high in [(96, 127), (128, 143), (144, 159)]:
        code += f'''  destruct (Z.leb {low} opcode && Z.leb opcode {high}). {{ reflexivity. }}
'''
    code += '''  rewrite op_12_eq. reflexivity.
Qed.
'''
    (output/'ContextHandlers.v').write_text(code)


def derive(name, expression, unfold, replacements, normalize=None):
    """Only replace named functions with already proved equal specializations."""
    code = f'''Definition raw_{name} := ltac:(
  let body := eval cbv beta iota zeta delta [{unfold}] in ({expression}) in
'''
    for original, arity, native in replacements:
        pattern = original if arity == 0 else '@' + original + ' ' + ' '.join('_' for _ in range(arity))
        code += f'''  let rec subst_term body := lazymatch body with
  | context C [{pattern}] => let body := context C [{native}] in subst_term body
  | _ => body end in
  let body := subst_term body in
'''
    code += '  exact body).\n'
    code += f'Definition {name} := '
    if normalize:
        code += f'Eval cbv beta iota zeta delta - [{normalize}] in '
    code += f'raw_{name}.\nLemma {name}_eq : {name} = {expression}.\nProof.\n'
    code += f'  change (raw_{name} = {expression}).\n  unfold raw_{name}.\n'
    for _, _, native in replacements:
        code += f'  rewrite !{native}_eq.\n'
    code += '  reflexivity.\nQed.\n'
    return code


def generate_context_runtime(root, output):
    keep = (output/'context_keep.txt').read_text() + ' native_dispatch'
    code = (output/'ContextOwned.v').read_text().split('Definition owned_account_load')[0]
    code += '''Require Import ContextOwned.
Require Import ContextHandlers.
Require Import RocqOfRust.revm.revm_interpreter.simulate.eth_interpreter.
Require Import RocqOfRust.revm.revm_interpreter.links.interpreter_action.
Require Import RocqOfRust.revm.revm_interpreter.simulate.interpreter_types.
Require Import RocqOfRust.revm.revm_context_interface.simulate.context.
Require Import RocqOfRust.revm.revm_handler.simulate.evm.
Require Import RocqOfRust.revm.revm_handler.simulate.frame.
Require Import RocqOfRust.revm.revm_handler.simulate.frame_data.
Require Import RocqOfRust.revm.revm_handler.simulate.handler.
Require Import RocqOfRust.revm.revm_handler.simulate.precompile_provider.
'''
    code += derive('native_step', 'RuntimeInterpreter.step (WIRE := WIRE) (H := ctx) (IInterpreterTypes := InterpreterTypes.I)',
                   'RuntimeInterpreter.step', [('RuntimeInstructionTable.execute', 7, 'native_dispatch')], keep)
    source = (root/'revm/revm_interpreter/simulate/runtime.v').read_text()
    body = definition_body(source.replace('Fixpoint run_plain', 'Definition run_plain'), 'run_plain')
    body = body.split('\nEnd RuntimeInterpreter.')[0].removesuffix('.')
    body = body.replace('step interpreter host', 'native_step interpreter host').replace('run_plain fuel', 'raw_run_plain fuel')
    code += f'''Fixpoint raw_run_plain (fuel : nat) (is_not_end : eth_types.Bytecode.t -> bool)
    (interpreter : machine) (host : ctx)
    : option (InterpreterAction.t * machine * ctx * nat) :=
  let IInterpreterTypes := InterpreterTypes.I in {body}.
Definition native_run_plain := Eval cbv beta iota zeta delta - [{keep} native_step] in raw_run_plain.
Lemma native_run_plain_eq : native_run_plain =
    RuntimeInterpreter.run_plain (WIRE := WIRE) (H := ctx) (IInterpreterTypes := InterpreterTypes.I).
Proof.
  change (raw_run_plain = RuntimeInterpreter.run_plain (WIRE := WIRE) (H := ctx) (IInterpreterTypes := InterpreterTypes.I)).
  apply functional_extensionality. intro fuel. induction fuel as [| fuel IH];
    apply functional_extensionality; intro is_not_end;
    apply functional_extensionality; intro interpreter;
    apply functional_extensionality; intro host.
  - cbn [raw_run_plain RuntimeInterpreter.run_plain].
    destruct (is_not_end interpreter.(Interpreter.bytecode)); reflexivity.
  - cbn [raw_run_plain RuntimeInterpreter.run_plain].
    destruct (is_not_end interpreter.(Interpreter.bytecode)); [| reflexivity].
    rewrite native_step_eq. destruct (RuntimeInterpreter.step interpreter host) as [[next_interpreter next_host] |]; [| reflexivity].
    rewrite IH. reflexivity.
Qed.
'''
    code += derive('native_eth_run', 'Impl_EthInterpreter.run_plain (H := ctx)',
                   'Impl_EthInterpreter.run_plain', [('RuntimeInterpreter.run_plain', 7, 'native_run_plain')])
    code += derive('native_frame_run', 'Impl_Evm.frame_run (DB := EestTypes.Input.t) (Error := unit)',
                   'Impl_Evm.frame_run', [('Impl_EthInterpreter.run_plain', 2, 'native_eth_run')])
    source = (root/'revm/revm_handler/simulate/evm.v').read_text()
    body = definition_body(source.replace('Fixpoint run ', 'Definition run '), 'run')
    body = body.replace('Impl_Evm.frame_run', 'native_frame_run')
    body = re.sub(r'\brun loop_bound', 'raw_exec_loop loop_bound', body)
    code += f'''Fixpoint raw_exec_loop (loop_bound fuel : nat) (self : Evm.t EestTypes.Input.t unit) {{struct loop_bound}}
    : option (Result.t FrameResult.t (ContextError.t unit) * Evm.t EestTypes.Input.t unit * nat) := {body}.
Definition native_exec_loop := raw_exec_loop.
Lemma native_exec_loop_eq : native_exec_loop =
    ExecutionLoop.run (DB := EestTypes.Input.t) (Error := unit).
Proof.
  unfold native_exec_loop. apply functional_extensionality. intro bound.
  induction bound as [| bound IH];
    apply functional_extensionality; intro fuel;
    apply functional_extensionality; intro evm.
  - reflexivity.
  - cbn [raw_exec_loop ExecutionLoop.run]. rewrite native_frame_run_eq.
    destruct (Impl_Evm.frame_run fuel evm) as [[[action self] next_fuel] |]; [| reflexivity].
    destruct action as [input | result]; cbn.
    + destruct (Impl_Evm.frame_init self input) as [[[item | error] self'] |]; try reflexivity.
      destruct item as [item | result].
      * rewrite IH. reflexivity.
      * destruct (Impl_Evm.frame_return_result self' result) as [[[returned | error] self''] |]; try reflexivity.
        destruct returned; [reflexivity | rewrite IH; reflexivity].
    + destruct (Impl_Evm.frame_return_result self result) as [[[returned | error] self'] |]; try reflexivity.
      destruct returned; [reflexivity | rewrite IH; reflexivity].
Qed.
'''
    code += derive('native_run_exec_loop', 'ExecutionLoop.run_exec_loop (DB := EestTypes.Input.t) (Error := unit)',
                   'ExecutionLoop.run_exec_loop', [('ExecutionLoop.run', 4, 'native_exec_loop')])
    code += derive('native_execution', 'Handler.execution (DB := EestTypes.Input.t) (Error := unit)',
                   'Handler.execution', [('ExecutionLoop.run_exec_loop', 4, 'native_run_exec_loop')])
    code += derive('native_run_without_catch_error', 'Handler.run_without_catch_error (DB := EestTypes.Input.t) (Error := unit)',
                   'Handler.run_without_catch_error', [('Handler.execution', 4, 'native_execution')])
    code += derive('native_handler_run', 'Handler.run (DB := EestTypes.Input.t) (Error := unit)',
                   'Handler.run', [('Handler.run_without_catch_error', 4, 'native_run_without_catch_error')])
    (output/'ContextRuntime.v').write_text(code)


def generate_context_transactions(root, output):
    code = (output/'ContextRuntime.v').read_text().split('Definition raw_native_step')[0]
    code += '''Require Import ContextRuntime.
Require Import RocqOfRust.revm.revm_handler.simulate.eest_transaction.
Require Import RocqOfRust.revm.revm_handler.simulate.transaction_accounting.
Require Import RocqOfRust.revm.revm_handler.simulate.transaction_auth.
Require Import RocqOfRust.revm.revm_handler.simulate.transaction_validation.
Require Import RocqOfRust.revm.revm_handler.simulate.ethereum_commitment.
Require Import RocqOfRust.revm.revm_interpreter.interpreter_action.links.create_inputs.
'''
    code += derive('native_transaction_run', 'EestContext.run', 'EestContext.run',
                   [('Handler.run', 4, 'native_handler_run')])
    code += '''Definition native_eest_transaction_run := EestTransaction.run_with native_transaction_run.
Lemma native_eest_transaction_run_eq : native_eest_transaction_run = EestTransaction.run.
Proof. unfold native_eest_transaction_run, EestTransaction.run. rewrite native_transaction_run_eq. reflexivity. Qed.
Set Extraction KeepSingleton.
Extraction Language OCaml.
Extraction Inline revm.revm_bytecode.links.bytecode.Bytecode.of_ty.
Extraction "@NATIVE_OUTPUT@/native_transactions.ml" native_transaction_run native_eest_transaction_run
  TransactionAuth.authenticate TransactionAuth.authenticate_for_spec
  TransactionValidation.validate EthereumCommitment.state_root EthereumCommitment.logs_hash.
'''
    (output/'NativeTransactions.v').write_text(code)
