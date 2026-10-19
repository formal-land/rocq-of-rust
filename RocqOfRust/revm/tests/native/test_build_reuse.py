import importlib.util
import json
from pathlib import Path
import sys
import subprocess
import tempfile
import types
import unittest
from unittest.mock import patch

# The generator is not exercised by cache metadata tests.
spec = importlib.util.spec_from_file_location('native_build', Path(__file__).with_name('build.py'))
build = importlib.util.module_from_spec(spec)
with patch.dict(sys.modules, {"generate": types.SimpleNamespace(generate=lambda *a, **kw: None)}):
    spec.loader.exec_module(build)


class BuildReuseTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.names = build.required_outputs(True, True)
        for name in self.names:
            (self.root / name).write_bytes(b'compiled artifact')
            (self.root / name).chmod(0o700)

    def test_matching_outputs_reuse(self):
        build.save_build_stamp(self.root, 'input-a', self.names)
        self.assertTrue(build.reusable_build(self.root, 'input-a', self.names))

    def test_changed_input_does_not_reuse(self):
        build.save_build_stamp(self.root, 'input-a', self.names)
        self.assertFalse(build.reusable_build(self.root, 'input-b', self.names))

    def test_changed_or_missing_executable_does_not_reuse(self):
        build.save_build_stamp(self.root, 'input-a', self.names)
        bridge = self.root / 'native_transaction_bridge'
        bridge.write_bytes(b'changed binary')
        self.assertFalse(build.reusable_build(self.root, 'input-a', self.names))
        bridge.unlink()
        self.assertFalse(build.reusable_build(self.root, 'input-a', self.names))

    def test_non_executable_bridge_does_not_reuse(self):
        build.save_build_stamp(self.root, 'input-a', self.names)
        (self.root / 'native_transaction_bridge').chmod(0o600)
        self.assertFalse(build.reusable_build(self.root, 'input-a', self.names))

    def test_different_requested_outputs_do_not_reuse(self):
        names = build.required_outputs(False, False)
        build.save_build_stamp(self.root, 'input-a', names)
        self.assertFalse(build.reusable_build(self.root, 'input-a', self.names))

    def test_absent_or_corrupt_stamp_does_not_reuse(self):
        stamp = self.root / 'build-success.json'
        self.assertFalse(build.reusable_build(self.root, 'input-a', self.names))
        for content in ['{partial', '[]', '{"outputs": []}']:
            stamp.write_text(content)
            self.assertFalse(build.reusable_build(self.root, 'input-a', self.names))

    def test_stamp_not_published_when_output_missing(self):
        (self.root / self.names[0]).unlink()
        with self.assertRaises(FileNotFoundError):
            build.save_build_stamp(self.root, 'input-a', self.names)
        self.assertFalse((self.root / 'build-success.json').exists())

    def test_build_lock_excludes_another_process_and_releases_on_error(self):
        command = [sys.executable, "-c", (
            "import fcntl, sys; "
            "f = open(sys.argv[1], 'a'); "
            "fcntl.flock(f.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)"
        ), str(self.root / '.build.lock')]
        with self.assertRaisesRegex(RuntimeError, 'interrupted'):
            with build.output_lock(self.root):
                result = subprocess.run(command, capture_output=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(b'BlockingIOError', result.stderr)
                raise RuntimeError('interrupted')
        self.assertEqual(subprocess.run(command, capture_output=True).returncode, 0)

    def test_fingerprint_covers_source_options_and_toolchain(self):
        sources = self.root / 'native'
        sources.mkdir()
        (sources / 'build.py').write_text('builder')
        for name in ['Makefile', '_RocqProject', 'blacklist.txt', 'input.v']:
            (self.root / name).write_text('input')
        tool = self.root / 'compiler'
        tool.write_text('compiler v1')
        def command_result(command, **kwargs):
            return types.SimpleNamespace(stdout=str(tool) if 'which' in command else 'version 1')
        with patch.object(build.subprocess, 'run', side_effect=command_result):
            def fingerprint(backend='zarith', smoke=True):
                return build.build_fingerprint(self.root, sources, [], backend, smoke, True)
            first = fingerprint()
            self.assertEqual(first, fingerprint())
            self.assertNotEqual(first, fingerprint('inductive'))
            self.assertNotEqual(first, fingerprint(smoke=False))
            (self.root / 'input.v').write_text('changed definition')
            second = fingerprint()
            self.assertNotEqual(first, second)
            tool.write_text('compiler changed with same version')
            self.assertNotEqual(second, fingerprint())


class CompilerLimitTests(unittest.TestCase):
    def test_child_limits_and_parent_isolation(self):
        import resource
        parent_limit = resource.getrlimit(resource.RLIMIT_AS)
        command = [sys.executable, "-c",
                   "import json, resource; print(json.dumps([resource.getrlimit(k) "
                   "for k in (resource.RLIMIT_AS, resource.RLIMIT_STACK, resource.RLIMIT_CORE)]))"]
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            for limit in (2048, 8192):
                kwargs = {} if limit == 2048 else {"memory_limit_mib": limit}
                build.run(command, output, "limits.log", **kwargs)
                self.assertEqual(json.loads((output / "limits.log").read_text()),
                                 [[limit * 1024**2] * 2, [64 * 1024**2] * 2, [0, 0]])
        self.assertEqual(resource.getrlimit(resource.RLIMIT_AS), parent_limit)

    def test_override_only_reaches_ocaml_compilation(self):
        with tempfile.TemporaryDirectory() as directory:
            arguments = ["build.py", "--output-dir", directory, "--smoke", "--bridge",
                         "--numeric-backend", "zarith", "--native-memory-limit-mib", "8192"]
            with patch.object(sys, "argv", arguments), patch.object(build, "run") as run:
                build.main()
            native_logs = {"numeric_shifts_build.log", "native_library.log",
                           "native_smoke_build.log", "native_authorization_build.log",
                           "native_bridge_build.log"}
            seen = set()
            for call in run.call_args_list:
                command, output, log, *limit = call.args
                if log in native_logs:
                    self.assertEqual(limit, [8192])
                    seen.add(log)
                else:
                    self.assertEqual(limit, [])
            self.assertEqual(seen, native_logs)

    def test_nonpositive_limit_rejected_before_build(self):
        for value in ("0", "-1"):
            with patch.object(sys, "argv", ["build.py", "--native-memory-limit-mib", value]):
                with self.assertRaises(SystemExit) as result:
                    build.main()
                self.assertEqual(result.exception.code, 2)


if __name__ == '__main__':
    unittest.main()
