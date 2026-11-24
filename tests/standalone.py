"""Integration checks for output paths and multi-module standalone translation."""
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess
import sys

binary = Path(sys.argv[1]).resolve()
with TemporaryDirectory() as root:
    cwd = Path(root)
    src = cwd / "src"
    src.mkdir()
    (src / "lib.rs").write_text("pub mod child; pub fn parent() {}")
    (src / "child.rs").write_text("pub fn leaf() {}")

    def translate(path, *args):
        return subprocess.run([binary, "translate", "--path", path, *args],
                              cwd=cwd, capture_output=True, text=True)

    for path in [".", "src", "./src/lib.rs"]:
        result = translate(path)
        assert result.returncode == 0, result.stderr
        dest = cwd / "rocq_translation" / "src"
        assert "Definition parent " in (dest / "lib.v").read_text()
        assert "Definition leaf " in (dest / "child.v").read_text()
        for file in dest.glob("*.v"):
            file.unlink()
    (src / "main.rs").touch()
    assert "explicit Rust file" in translate(".").stderr
    assert translate("src/lib.rs", "--output-path", "src/main.rs").returncode != 0
