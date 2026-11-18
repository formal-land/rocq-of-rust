"""Check output completeness as Cargo switches between fresh and dirty builds."""
from pathlib import Path
from tempfile import TemporaryDirectory
import os
import subprocess
import sys

bin_dir = Path(sys.argv[1]).resolve()
with TemporaryDirectory() as temp:
    crate = Path(temp)
    src = crate / "src"
    src.mkdir()
    (crate / "Cargo.toml").write_text('[package]\nname="warm"\nversion="0.1.0"\nedition="2021"\n')
    (src / "lib.rs").write_text("pub mod child; pub fn root() -> u8 { child::leaf() }")
    (src / "child.rs").write_text("pub fn leaf() -> u8 { 9 }")
    env = {**os.environ, "PATH": str(bin_dir) + os.pathsep + os.environ["PATH"],
           "CARGO_TARGET_DIR": str(crate / "target"), "CARGO_NET_OFFLINE": "true"}

    def cargo(*args):
        subprocess.run(["cargo", *args], cwd=crate, env=env, check=True)

    cargo("check")
    cargo("rocq-of-rust")
    root = src / "lib.v"
    index = crate / "warm.v"
    assert index.read_text().splitlines() == ["Require Export src.child.", "Require Export src.lib."]
    normal = root.read_bytes()
    child = src / "child.v"
    expected = child.read_bytes()
    child.unlink()
    cargo("rocq-of-rust")
    assert child.read_bytes() == expected
    cargo("rocq-of-rust", "--axiomatize", "--with-json")
    assert root.read_bytes() != normal
    assert (src / "child.json").is_file()
    (src / "lib.json").unlink()
    cargo("rocq-of-rust", "--axiomatize", "--with-json")
    assert (src / "lib.json").is_file()
    cargo("rocq-of-rust")
    assert root.read_bytes() == normal
    stamp = root.stat().st_mtime_ns
    cargo("rocq-of-rust")
    assert root.stat().st_mtime_ns == stamp
