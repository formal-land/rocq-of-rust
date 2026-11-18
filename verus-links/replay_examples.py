"""Run the end-to-end bridge examples and mutation controls with the installed tools."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-path', required=True, type=Path)
    args = parser.parse_args()
    args.output_path.mkdir(parents=True, exist_ok=True)
    root = Path(tempfile.mkdtemp(prefix='suite-', dir=args.output_path.resolve()))
    cli = os.environ.get('ROCQ_OF_RUST', 'rocq-of-rust')
    results = {}

    def check(case, source, function, proof=None, *, at=None, code=0, message=None):
        command = [cli, 'verus', '--path', source, '--function', function, '--output-path', root/case]
        if proof:
            command += ['--proof', proof]
        if at:
            command += ['--at', at]
        p = subprocess.run(command, text=True, capture_output=True)
        if not p.stdout.strip():
            raise RuntimeError(p.stderr)
        report = json.loads(p.stdout)
        results[case] = report
        (root/'suite.json').write_text(json.dumps(results, indent=2)+'\n')
        if p.returncode != code or (message and message not in json.dumps(report)):
            raise AssertionError(f'{case}: exit {p.returncode}\n{report}')
        print(f'{case}: Verus {report.get("verus")}, Rocq {report["rocq"]} (exit {code})', flush=True)
        return Path(report['directory'])

    def mutant(case, base, before, after):
        text = base.read_text()
        if text.count(before) != 1:
            raise ValueError(f'{case} mutation no longer matches a unique source range')
        path = root/'inputs'/case/base.name
        path.parent.mkdir(parents=True)
        path.write_text(text.replace(before, after))
        return path

    nested, fill, point = (HERE/f for f in ('nested.rs', 'fill.rs', 'checkpoint.rs'))
    for fn, prefix in [('swap', 'Swap'), ('left_mut', 'Borrow'), ('write_twice', 'Twice')]:
        check(fn, nested, fn, HERE/(prefix+'Proof.v'))
    check('inline-assertion', point, 'set_word', HERE/'CheckpointProof.v', at='7:23')
    full_run = check('fill', fill, 'fill_prefix', HERE/'FillProof.v')
    check('selected-invariant', fill, 'fill_prefix', at='20:24', message='invariant_3')
    missing = mutant('missing-invariant', fill,
                     '            forall|j: int| i <= j < old(xs)@.len() ==> xs@[j] == old(xs)@[j],\n', '')
    fallback = check('fallback', missing, 'fill_prefix', HERE/'FillProof.v', code=2)
    check('selected-suffix', missing, 'fill_prefix', HERE/'FillSuffixProof.v', at='11:9', code=2)
    compound = mutant('compound', fill, 'i = i + 1;', 'i += 1;')
    check('compound-assignment', compound, 'fill_prefix', HERE/'FillProof.v')
    original_body = (full_run/'fill.v').read_text().split('Definition fill_prefix ', 1)[1]
    fallback_body = (fallback/'fill.v').read_text().split('Definition fill_prefix ', 1)[1]
    if original_body != fallback_body:
        raise AssertionError('removing a specification invariant changed the translated body')
    if 'failed this postcondition' not in (fallback/'verus.log').read_text():
        raise AssertionError('expected a source-located Verus postcondition diagnostic')
    if 'TodoLoop' in (fallback/'Replay.log').read_text():
        raise AssertionError('loop execution still uses the placeholder')
    bad = mutant('false-contract', nested, 'final(p).pair.left == second', 'final(p).pair.left == first')
    check('false-contract', bad, 'write_twice', HERE/'TwiceProof.v', code=1, message='TwiceProof.log')
    bad = mutant('wrong-write', nested, '*r = second;', '*r = first;')
    check('wrong-write', bad, 'write_twice', HERE/'TwiceProof.v', code=1, message='TwiceProof.log')
    moved = mutant('moved', point, '    *p = x;\n', '')
    moved.write_text(moved.read_text().replace('proof! { assert(*p == x); }','proof! { assert(*p == x); }\n    *p = x;'))
    check('moved-assertion', moved, 'set_word', HERE/'CheckpointProof.v', at='6:23', code=1, message='Replay.log')
    unrelated = root/'inputs'/'unrelated'
    unrelated.mkdir()
    for name in ['SwapLink.v','NestedSupport.v']:
        shutil.copyfile(HERE/name, unrelated/name)
    proof = unrelated/'SwapProof.v'
    proof.write_text('Theorem checked_execution : True. Proof. exact I. Qed.\n')
    check('unrelated-proof',nested,'swap',proof,code=1,message='Replay.log')
    proof.write_text('Require Import SwapLink BridgeContract.\nAxiom checked_execution : execution_claim pre post.\n')
    check('admitted-proof',nested,'swap',proof,code=1,message='introduced assumptions')
    bad = mutant('unsupported',nested,'final(p).pair.left == second','final(p).pair.left != first')
    check('unsupported',bad,'write_twice',code=1,message='unsupported')
    renamed = mutant('renamed',nested,'pub fn swap(', 'pub fn exchange(')
    check('renamed',renamed,'exchange')
    different = mutant('different-bodies',nested,'    *r = second;', '    #[cfg(not(verus_only))]\n    { *r = second; }')
    check('different-bodies',different,'write_twice',code=1,message='conditional executable Rust')
    # Original three-function shallow exporter and simulation proofs.
    legacy = root/'pair'
    legacy.mkdir()
    shutil.copyfile(HERE/'pair.rs', legacy/'pair.rs')
    def run(cmd):
        subprocess.run(cmd,cwd=legacy,check=True,stdout=log,stderr=subprocess.STDOUT)
    with (legacy/'pair.log').open('w') as log:
        run([os.environ.get('VERUS','verus'),'--crate-type','lib','--log','vir','--no-cheating','pair.rs'])
        run([sys.executable,HERE/'export_contracts.py','.verus-log/crate.vir','Contracts.v'])
        run([cli,'translate','--path','pair.rs','--output-path','.'])
        for name in ['View','PairProof']:
            shutil.copyfile(HERE/(name+'.v'),legacy/(name+'.v'))
        lib = Path(os.environ['ROCQ_OF_RUST_LIB']).resolve()
        for name in ['Contracts','pair','View','PairProof']:
            run([os.environ.get('COQC','coqc'),'-q','-Q','.','','-R',lib,'RocqOfRust',
                 '-I',lib/'plugin','-impredicative-set',name+'.v'])
    print('original pair proofs checked. Results in',root,flush=True)


if __name__ == '__main__':
    main()
