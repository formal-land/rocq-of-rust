#!/usr/bin/env python3

import argparse
import re
import resource
import shutil
import subprocess
import time
from pathlib import Path

from generate import generate


MODULES = [
    "OwnedAccountLoad", "CallHelpers", "OwnedHost", "Handlers", "NativeStep",
    "FrameHelpers", "NativeRuntime", "NativeTransactions",
]


def compiler_limits():
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))
    resource.setrlimit(resource.RLIMIT_STACK, (64 * 1024**2, 64 * 1024**2))


def run(command, output, log_name):
    started = time.monotonic()
    log = output/log_name
    with log.open("w") as stream:
        result = subprocess.run(
            command, cwd=output, stdout=stream, stderr=subprocess.STDOUT,
            preexec_fn=compiler_limits, check=False,
        )
    if result.returncode:
        raise SystemExit(f"Command failed ({result.returncode}); see {log}")
    print(f"{log_name}: passed in {time.monotonic()-started:.1f}s", flush=True)


def check_extraction(output):
    for source in output.glob("*.ml"):
        if re.search(r'failwith\s+"AXIOM TO BE REALIZED', source.read_text()):
            raise SystemExit(f"Computational axiom placeholder in {source}")


def main():
    parser = argparse.ArgumentParser(description="Build the proved concrete REVM extraction")
    parser.add_argument("--rocq-root", type=Path)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--opam-switch")
    parser.add_argument("--smoke", action="store_true", help="Run sixteen native transaction checks")
    parser.add_argument("--bridge", action="store_true", help="Build the full-state JSONL bridge")
    parser.add_argument("--numeric-backend", choices=["inductive", "zarith"],
                        default="inductive", help="Optional Zarith extraction; requires differential validation")
    args = parser.parse_args()
    sources = Path(__file__).resolve().parent
    root = (args.rocq_root or sources.parents[2]).resolve()
    output = (args.output_dir or root.parent/"target"/"revm-native").resolve()
    dependencies = [
        "revm/revm_handler/simulate/legacy_call.vo",
        "revm/revm_handler/simulate/eest_transaction.vo",
        "revm/revm_handler/simulate/transaction_auth.vo",
        "revm/revm_handler/simulate/ethereum_commitment.vo",
    ]
    prefix = ["opam", "exec", f"--switch={args.opam_switch}", "--"] if args.opam_switch else []
    output.mkdir(parents=True, exist_ok=True)
    run(prefix+["make", "-C", str(root), "-j1", *dependencies], output,
        "canonical_dependencies.log")
    generate(root, output, sources/"templates", numeric_backend=args.numeric_backend)
    flags = [
        "-I", str(root/"plugin"), "-R", str(root), "RocqOfRust",
        "-Q", str(output), "", "-impredicative-set",
    ]
    modules = MODULES + (["NativeTransactionSmoke"] if args.smoke else [])
    for module in modules:
        run(prefix+["coqc"]+flags+[str(output/f"{module}.v")], output, f"{module}.log")
    check_extraction(output)
    numeric_objects = []
    if args.numeric_backend == "zarith":
        shutil.copyfile(sources/"native_numeric_shifts.ml", output/"native_numeric_shifts.ml")
        run(prefix+["ocamlfind", "ocamlopt", "-package", "zarith", "-c", "native_numeric_shifts.ml"],
            output, "numeric_shifts_build.log")
        numeric_objects = ["native_numeric_shifts.cmx"]
    run(prefix+["ocamlfind", "ocamlopt", "-package", "zarith", "-w", "-a", "-c", "native_transactions.mli", "native_transactions.ml"],
        output, "native_library.log")
    if args.smoke:
        run(prefix+["ocamlfind", "ocamlopt", "-package", "zarith", "-linkpkg", "-w", "-a", "-o", "native_transaction_smokes"]+numeric_objects+[
                    "native_transaction_smoke.mli", "native_transaction_smoke.ml", "native_transaction_main.ml"],
            output, "native_smoke_build.log")
        run([str(output/"native_transaction_smokes")], output, "native_smoke_run.log")
    if args.bridge:
        shutil.copyfile(sources/"native_transaction_bridge.ml", output/"native_transaction_bridge.ml")
        shutil.copyfile(sources/f"native_numeric_{args.numeric_backend}.ml", output/"native_numeric.ml")
        run(prefix+["ocamlfind", "ocamlopt", "-w", "-a", "-package", "yojson,zarith", "-linkpkg",
                    *numeric_objects, "native_transactions.cmx", "native_numeric.ml", "native_transaction_bridge.ml", "-o", "native_transaction_bridge"],
            output, "native_bridge_build.log")
    print(f"Native transaction extraction: {output}")


if __name__ == "__main__":
    main()
