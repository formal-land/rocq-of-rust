#!/usr/bin/env bash
set -euo pipefail
translator=$(realpath "${1:?pass the built rocq-of-rust binary}")
cd "$(dirname "$0")"
project=$(realpath ../../RocqOfRust)
export LD_LIBRARY_PATH="$(rustc --print sysroot)/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export OCAMLPATH="$project/plugin${OCAMLPATH:+:$OCAMLPATH}"
make -C "$project" -j1 evaluate/RocqOfRust.vo lib/simulate/lib.vo core/char/methods.vo core/slice/simulate/mod.vo core/simulate/option.vo alloc/vec/simulate/mod.vo
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
flags=(-R "$project" RocqOfRust -I "$project/plugin" -impredicative-set -Q "$work" ReleaseTests)
for source in *.rs; do
  name=${source%.rs}
  rustc -C overflow-checks=off "$source" -o "$work/native"
  "$work/native"
  if ! "$translator" translate --path "$source" --output-path "$work" 2>"$work/$name.err"; then
    cat "$work/$name.err" >&2
    exit 1
  fi
  cat "$work/$name.err" >&2
  if [[ -f "$name.warnings" ]]; then
    sed -n 's/^warning: \(\[ROR[0-9]*\].*\)$/\1/p' "$work/$name.err" | sort > "$work/warnings"
    diff -u "$name.warnings" "$work/warnings"
  fi
  coqc "${flags[@]}" "$work/$name.v"
  cp "${name}_check.v" "$work/"
  coqc "${flags[@]}" "$work/${name}_check.v"
done
cp core_char.v "$work/"
coqc "${flags[@]}" "$work/core_char.v"
cp assumptions.v "$work/"
coqc "${flags[@]}" "$work/assumptions.v" | tee "$work/assumptions.log"
python3 summarize_assumptions.py < "$work/assumptions.log" > "$work/assumptions.actual"
diff -u assumptions.expected "$work/assumptions.actual"
python3 exhaustive_division.py
