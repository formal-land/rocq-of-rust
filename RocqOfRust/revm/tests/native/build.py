#!/usr/bin/env python3

import argparse
from contextlib import contextmanager
import fcntl
from functools import partial
import hashlib
import json
import os
import tempfile
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


def compiler_limits(memory_limit_mib=2048):
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    resource.setrlimit(resource.RLIMIT_AS, (memory_limit_mib * 1024**2, memory_limit_mib * 1024**2))
    resource.setrlimit(resource.RLIMIT_STACK, (64 * 1024**2, 64 * 1024**2))


def run(command, output, log_name, memory_limit_mib=2048):
    started = time.monotonic()
    log = output/log_name
    with log.open("w") as stream:
        result = subprocess.run(
            command, cwd=output, stdout=stream, stderr=subprocess.STDOUT,
            preexec_fn=partial(compiler_limits, memory_limit_mib), check=False,
        )
    if result.returncode:
        raise SystemExit(f"Command failed ({result.returncode}); see {log}")
    print(f"{log_name}: passed in {time.monotonic()-started:.1f}s", flush=True)


def check_extraction(output):
    for source in output.glob("*.ml"):
        if re.search(r'failwith\s+"AXIOM TO BE REALIZED', source.read_text()):
            raise SystemExit(f"Computational axiom placeholder in {source}")


# Conservative local reuse: all Rocq sources are inputs, not just direct imports.
# This deliberately invalidates more often than a dependency-specific cache.
# Installed dependency packages are assumed immutable at their reported versions.
# After manually editing installed libraries, use --no-cache instead of --reuse.
def file_digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_fingerprint(root, sources, prefix, numeric_backend, smoke, bridge):
    paths = set(root.rglob("*.v"))
    paths.update(path for path in (root / "plugin").rglob("*")
                 if path.is_file() and path.suffix in {".ml", ".mli"})
    paths.update(path for path in sources.rglob("*")
                 if path.is_file() and "__pycache__" not in path.parts)
    paths.update(root / name for name in ["Makefile", "_RocqProject", "blacklist.txt"])
    inputs = {str(path.resolve()): file_digest(path) for path in sorted(paths)}
    toolchain = []
    for command in [["coqc", "--version"], ["ocamlopt", "-config"],
                    ["ocamlfind", "list"], ["make", "--version"]]:
        result = subprocess.run(prefix + command, check=True, capture_output=True, text=True)
        toolchain.append(result.stdout)
    # Include executable contents and paths, not only version strings. Resolve
    # inside opam when a switch is selected, just like the build commands.
    for name in ["coqc", "ocamlopt", "ocamlfind", "make"]:
        result = subprocess.run(prefix + ["which", name], check=True,
                                capture_output=True, text=True)
        path = Path(result.stdout.strip()).resolve()
        toolchain.append([str(path), file_digest(path)])
    identity = {
        "schema": 1, "inputs": inputs, "toolchain": toolchain,
        "prefix": prefix, "numeric_backend": numeric_backend,
        "smoke": smoke, "bridge": bridge,
        "environment": {name: os.environ.get(name) for name in
                        ["OCAMLPATH", "COQPATH", "ROCQPATH", "OCAMLPARAM", "OPAM_SWITCH_PREFIX"]},
    }
    return hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()


def required_outputs(smoke, bridge):
    names = ["native_transactions.cmx", "native_transactions.o", "native_transactions.cmi"]
    if smoke:
        names += ["native_transaction_smokes", "native_authorization_smokes"]
    if bridge:
        names.append("native_transaction_bridge")
    return names


def reusable_build(output, fingerprint, names):
    try:
        stamp = json.loads((output / "build-success.json").read_text())
        return (isinstance(stamp, dict) and isinstance(stamp.get("outputs"), dict)
                and stamp.get("fingerprint") == fingerprint
                and set(stamp.get("outputs", {})) == set(names)
                and all(file_digest(output / name) == stamp["outputs"][name]
                        and (Path(name).suffix or os.access(output / name, os.X_OK))
                        for name in names))
    except (OSError, ValueError, TypeError, KeyError):
        return False


def save_build_stamp(output, fingerprint, names):
    stamp = {"fingerprint": fingerprint,
             "outputs": {name: file_digest(output / name) for name in names}}
    # A failed or interrupted build must never publish a partial success stamp.
    with tempfile.NamedTemporaryFile(mode="w", dir=output, delete=False) as stream:
        temporary = Path(stream.name)
        json.dump(stamp, stream, sort_keys=True)
        stream.flush()
        os.fsync(stream.fileno())
    try:
        temporary.replace(output / "build-success.json")
    finally:
        temporary.unlink(missing_ok=True)


@contextmanager
def output_lock(output):
    # Keep the lock file: unlinking it permits another process to lock a new inode.
    with (output / ".build.lock").open("a") as stream:
        try:
            fcntl.flock(stream.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise SystemExit(f"Another native build is using {output}")
        try:
            yield
        finally:
            fcntl.flock(stream.fileno(), fcntl.LOCK_UN)


def main():
    parser = argparse.ArgumentParser(description="Build the proved concrete REVM extraction")
    parser.add_argument("--rocq-root", type=Path)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--opam-switch")
    parser.add_argument("--native-memory-limit-mib", type=int, default=2048,
                        help="Address-space cap for OCaml compilation only (default: 2048 MiB)")
    parser.add_argument("--smoke", action="store_true", help="Run sixteen transaction and three authorization checks")
    parser.add_argument("--bridge", action="store_true", help="Build the full-state JSONL bridge")
    parser.add_argument("--numeric-backend", choices=["inductive", "zarith"],
                        default="inductive", help="Optional Zarith extraction; requires differential validation")
    cache = parser.add_mutually_exclusive_group()
    cache.add_argument("--reuse", action="store_true",
                       help="Reuse matching local inputs/outputs; assumes installed dependency packages are unmodified")
    cache.add_argument("--no-cache", action="store_true", help="Force a full native build (the default)")
    args = parser.parse_args()
    if args.native_memory_limit_mib <= 0:
        parser.error("--native-memory-limit-mib must be positive")
    sources = Path(__file__).resolve().parent
    root = (args.rocq_root or sources.parents[2]).resolve()
    output = (args.output_dir or root.parent/"target"/"revm-native").resolve()
    dependencies = [
        "revm/revm_handler/simulate/legacy_call.vo",
        "revm/revm_handler/simulate/eest_transaction.vo",
        "revm/revm_handler/simulate/transaction_auth.vo",
        "revm/revm_handler/simulate/transaction_validation.vo",
        "revm/revm_handler/simulate/ethereum_commitment.vo",
    ]
    if args.smoke:
        dependencies.append("alloy_eip7702/tests/auth_list.vo")
    prefix = ["opam", "exec", f"--switch={args.opam_switch}", "--"] if args.opam_switch else []
    output.mkdir(parents=True, exist_ok=True)
    with output_lock(output):
        fingerprint = None
        names = required_outputs(args.smoke, args.bridge)
        if args.reuse:
            fingerprint = build_fingerprint(root, sources, prefix, args.numeric_backend,
                                            args.smoke, args.bridge)
            if reusable_build(output, fingerprint, names):
                if args.smoke:
                    run([str(output/"native_transaction_smokes")], output, "native_smoke_run.log")
                    run([str(output/"native_authorization_smokes")], output, "native_authorization_run.log")
                print(f"Reused verified native transaction extraction: {output}")
                return
        (output / "build-success.json").unlink(missing_ok=True)
        run(prefix+["make", "-C", str(root), "-j1", *dependencies], output,
            "canonical_dependencies.log")
        generate(root, output, sources/"templates", numeric_backend=args.numeric_backend)
        flags = [
            "-I", str(root/"plugin"), "-R", str(root), "RocqOfRust",
            "-Q", str(output), "", "-impredicative-set",
        ]
        modules = MODULES + (["NativeTransactionSmoke", "NativeAuthorizationSmoke"] if args.smoke else [])
        for module in modules:
            run(prefix+["coqc"]+flags+[str(output/f"{module}.v")], output, f"{module}.log")
        check_extraction(output)
        numeric_objects = []
        if args.numeric_backend == "zarith" or args.smoke:
            shutil.copyfile(sources/"native_numeric_shifts.ml", output/"native_numeric_shifts.ml")
            run(prefix+["ocamlfind", "ocamlopt", "-package", "zarith", "-c", "native_numeric_shifts.ml"],
                output, "numeric_shifts_build.log", args.native_memory_limit_mib)
            if args.numeric_backend == "zarith":
                numeric_objects = ["native_numeric_shifts.cmx"]
        run(prefix+["ocamlfind", "ocamlopt", "-package", "zarith", "-w", "-a", "-c", "native_transactions.mli", "native_transactions.ml"],
            output, "native_library.log", args.native_memory_limit_mib)
        if args.smoke:
            run(prefix+["ocamlfind", "ocamlopt", "-package", "zarith", "-linkpkg", "-w", "-a", "-o", "native_transaction_smokes"]+numeric_objects+[
                        "native_transaction_smoke.mli", "native_transaction_smoke.ml", "native_transaction_main.ml"],
                output, "native_smoke_build.log", args.native_memory_limit_mib)
            run([str(output/"native_transaction_smokes")], output, "native_smoke_run.log")
            run(prefix+["ocamlfind", "ocamlopt", "-package", "zarith", "-linkpkg", "-w", "-a",
                        "-o", "native_authorization_smokes", "native_numeric_shifts.cmx",
                        "native_authorization_smoke.mli", "native_authorization_smoke.ml",
                        "native_authorization_main.ml"], output, "native_authorization_build.log", args.native_memory_limit_mib)
            run([str(output/"native_authorization_smokes")], output, "native_authorization_run.log")
        if args.bridge:
            shutil.copyfile(sources/"native_transaction_bridge.ml", output/"native_transaction_bridge.ml")
            shutil.copyfile(sources/f"native_numeric_{args.numeric_backend}.ml", output/"native_numeric.ml")
            run(prefix+["ocamlfind", "ocamlopt", "-w", "-a", "-package", "yojson,zarith", "-linkpkg",
                        *numeric_objects, "native_transactions.cmx", "native_numeric.ml", "native_transaction_bridge.ml", "-o", "native_transaction_bridge"],
                output, "native_bridge_build.log", args.native_memory_limit_mib)
        if args.reuse:
            current = build_fingerprint(root, sources, prefix, args.numeric_backend,
                                        args.smoke, args.bridge)
            if current == fingerprint:
                save_build_stamp(output, fingerprint, names)
            else:
                print("Build inputs changed during compilation; reuse stamp not saved.")
        print(f"Native transaction extraction: {output}")


if __name__ == "__main__":
    main()
