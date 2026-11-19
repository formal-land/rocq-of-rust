"""Compare the checkout's extracted checked i8 division/remainder with native Rust."""
from collections import Counter
import csv
from pathlib import Path
import shutil
import subprocess
from tempfile import TemporaryDirectory

here = Path(__file__).resolve().parent
core = here.parents[1] / "RocqOfRust"
with TemporaryDirectory() as tmp:
    wd = Path(tmp)
    shutil.copy(here / "ExtractArith.v", wd)
    def run(*args):
        return subprocess.run(args, cwd=wd, check=True, text=True, stdout=subprocess.PIPE).stdout
    run("coqc", "-R", str(core), "RocqOfRust", "-I", str(core / "plugin"),
        "-impredicative-set", "ExtractArith.v")
    (wd / "emit.ml").write_text("""let show = function None -> "_" | Some v -> string_of_int v
let () =
  for a = -128 to 127 do for b = -128 to 127 do
    let (q,r) = Extracted.pair_checked a b in
    Printf.printf "%d,%d,%s,%s\\n" a b (show q) (show r)
  done done
""")
    (wd / "oracle.rs").write_text("""fn show(v: Option<i8>) -> String {
    v.map(|x| x.to_string()).unwrap_or("_".into())
}
fn main() {
    for a in i8::MIN..=i8::MAX {
        for b in i8::MIN..=i8::MAX {
            println!("{a},{b},{},{}", show(a.checked_div(b)), show(a.checked_rem(b)));
        }
    }
}
""")
    run("ocamlopt", "extracted.mli", "extracted.ml", "emit.ml", "-o", "model")
    run("rustc", "oracle.rs", "-o", "oracle")
    native = list(csv.reader(run("./oracle").splitlines()))
    model = list(csv.reader(run("./model").splitlines()))
    assert len(native) == len(model) == 65536
    counts = Counter()
    for left, right in zip(native, model, strict=True):
        assert left[:2] == right[:2]
        for i, op in [(2,"checked_div"), (3,"checked_rem")]:
            if left[i] != right[i]:
                counts[op] += 1
    print("Different results across all 65,536 i8 input pairs:", dict(counts))
    if counts:
        raise SystemExit("Checked arithmetic disagrees with Rust")
