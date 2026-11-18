"""Export and replay Verus source contracts using a freshly translated Rust body."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

from vir_contract import generate

HERE = Path(__file__).resolve().parent
PIN = '8bf68ee741df833ea5d0fe6a2255126fdea87e47'
MODULE = re.compile(r'[A-Za-z][A-Za-z0-9_]*\Z')


def run(argv, cwd, log, *, check=True):
    p = subprocess.run(argv, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    (cwd/log).write_text(p.stdout+p.stderr)
    if check and p.returncode:
        raise ValueError(f"{argv[0]} failed. See {cwd/log}\n{p.stderr[-1800:]}")
    return p


def compile_proof(work, src, proof, crate, result):
    lib = Path(os.environ['ROCQ_OF_RUST_LIB']).resolve()
    command = [os.environ.get('COQC','coqc'), '-q', '-Q', '.', '', '-R', str(lib), 'RocqOfRust',
               '-I', str(lib/'plugin'), '-impredicative-set']
    def check(name):
        return run([*command, name+'.v'],work,name+'.log').stdout
    checked = {'Assertion', 'BridgeContract', crate}
    for module in ('Assertion', crate, 'BridgeContract'):
        check(module)
    if not proof.name.endswith('Proof.v') or not MODULE.fullmatch(proof.stem):
        raise ValueError('expected a file named <Name>Proof.v')
    link = proof.stem[:-5]+'Link'
    active = set()
    def local_module(name):
        if name in checked:
            return
        if name in active:
            raise ValueError(f"cyclic proof import {name}")
        active.add(name)
        source = (src/(name+'.v')).read_text()
        # Load only fresh sources. Explicit unqualified local Require imports are supported.
        for depgroup in re.findall(r'(?m)^Require\s+(?:(?:Export|Import)\s+)?([\w.\s]+?)\.(?=\s|$)',source):
            for dep in depgroup.split():
                if MODULE.fullmatch(dep) and (src/(dep+'.v')).is_file():
                    local_module(dep)
        (work/(name+'.v')).write_text(source)
        check(name)
        active.remove(name)
        checked.add(name)
    local_module(link)
    local_module(proof.stem)
    signature = f'{link}.execution_claim BridgeContract.pre BridgeContract.post'
    anchor = ''
    if result['site'].startswith(('assert_', 'invariant_')):
        anchor = (f'Check (eq_refl : {link}.linked_source_sha256 = '
                  f'("{result["sha256"]}"%string)).')
    (work/'Replay.v').write_text(f'''Require {link} {proof.stem} BridgeContract.
Require Import Stdlib.Strings.String.
{anchor}
Check (eq_refl : {link}.linked_function = BridgeContract.target_function).
Check (eq_refl : {link}.linked_site = BridgeContract.target_site).
Check (eq_refl : Assertion.covered {link}.observed_paths BridgeContract.pre_syntax = true).
Check (eq_refl : Assertion.covered {link}.observed_paths BridgeContract.post_syntax = true).
Definition replay : {signature} := {proof.stem}.checked_execution.
Print Assumptions replay.
''')
    # The trusted execution link fixes the theorem. Audit new assumptions in the
    # proof separately from the dependencies already present in its statement.
    (work/'LinkAudit.v').write_text(f'Require {link} BridgeContract.\nDefinition statement := {signature}.\nPrint Assumptions statement.\n')
    before = check('LinkAudit')
    after = check('Replay')
    def axioms(report):
        if 'Axioms:' not in report:
            if 'Closed under the global context' not in report and 'Theory:' not in report:
                raise ValueError('unrecognized Rocq assumptions report')
            return set()
        axioms = report.split('Axioms:',1)[1].split('Theory:',1)[0]
        return set(re.findall(r'(?m)^([^\s:]+)\s*:', axioms))
    if after.partition('Theory:')[2].strip() != before.partition('Theory:')[2].strip():
        raise ValueError('proof changed the logical assumptions of its execution statement')
    extra = axioms(after)-axioms(before)
    if extra:
        raise ValueError('proof introduced assumptions outside the reviewed execution statement: '+', '.join(sorted(extra)))
    return {'proof':proof.name,'link':link+'.v','assumptions':'Replay.log'}


def check_bridge(args, work, result):
    source=args.path.resolve()
    crate=source.stem
    if not MODULE.fullmatch(crate) or crate in {'Assertion','BridgeContract','Replay','LinkAudit'}:
        raise ValueError('expected a standalone Rust source file with a module-safe crate name')
    path=args.function if '::' in args.function else crate+'::'+args.function
    if not re.fullmatch(r'[A-Za-z_]\w*(?:::[A-Za-z_]\w*)+', path, re.ASCII) or path.split('::')[0]!=crate:
        raise ValueError('function must belong to the input crate')
    shutil.copyfile(source,work/source.name)
    result.update(function=path, source=str(source), sha256=hashlib.sha256((work/source.name).read_bytes()).hexdigest())
    verifier=os.environ.get('VERUS','verus')
    p=run([verifier,'--crate-type','lib','--no-cheating','--output-json','--log','vir',source.name],
          work,'verus.log',check=False)
    result['verus']='frontend or tool error'
    report=json.loads(p.stdout)
    version=report['verus']
    result['verus_version']=version
    if version['commit']!=PIN or version['platform']!={'arch':'x86_64','os':'linux'}:
        raise ValueError('unsupported Verus version or platform')
    stats=report['verification-results']
    if stats['encountered-vir-error'] or not stats['is-verifying-entire-crate'] or (
            p.returncode and not stats['errors']) or (not p.returncode)!=stats['success']:
        raise ValueError(f'Verus did not complete verification. See {work}/verus.log')
    if stats['success']:
        outcome = 'verified'
    elif re.search(r'(?i)resource limit|timed out|timeout|solver.*unknown', p.stderr):
        outcome = 'solver inconclusive'
    else:
        outcome = 'open obligations'
    result.update(verus=outcome,verus_crate=stats)
    contract,sites,site=generate((work/'.verus-log/crate.vir').read_text(),path,args.at)
    (work/'BridgeContract.v').write_text(contract)
    result.update(site=site, obligations=sites)
    shutil.copyfile(HERE/'Assertion.v',work/'Assertion.v')
    run([args.translator,'translate','--check-verus-input','--path',source.name,'--output-path','.'],work,'translation.log')
    if not (work/(crate+'.v')).is_file():
        raise ValueError('translator did not emit the Rust body')
    result['rocq']='exported only'
    if args.proof:
        result['rocq']='unchecked'
        proof=args.proof.resolve()
        result.update(compile_proof(work,proof.parent,proof,crate,result))
        result['rocq']='checked execution'


def location(text):
    if not re.fullmatch(r'[1-9]\d*:[1-9]\d*',text):
        raise argparse.ArgumentTypeError('expected LINE:COLUMN, starting at 1')
    return tuple(map(int,text.split(':')))


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--path',required=True,type=Path)
    p.add_argument('--output-path',required=True,type=Path)
    p.add_argument('--function',required=True)
    p.add_argument('--at',type=location)
    p.add_argument('--proof',type=Path)
    p.add_argument('--translator',default='rocq-of-rust',help=argparse.SUPPRESS)
    args=p.parse_args()
    args.output_path.mkdir(parents=True,exist_ok=True)
    work=Path(tempfile.mkdtemp(prefix='run-',dir=args.output_path.resolve()))
    result={'rocq':'unchecked','directory':str(work)}
    try:
        check_bridge(args, work, result)
    except (OSError, ValueError, KeyError, IndexError) as error:
        result['error']=str(error)
    (work/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('obligations','verus_version','verus_crate')},indent=2))
    if 'error' in result:
        return 1
    if result['verus'] != 'verified':
        return 2 if result['rocq'] == 'checked execution' else 3
    return 0


if __name__=='__main__':
    sys.exit(main())
