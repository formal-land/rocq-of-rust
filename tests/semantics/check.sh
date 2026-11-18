#!/usr/bin/env bash
set -euo pipefail
translator=$(realpath "${1:?pass the built rocq-of-rust binary}")
cd "$(dirname "$0")"
project=$(realpath ../../RocqOfRust)
export LD_LIBRARY_PATH="$(rustc --print sysroot)/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export OCAMLPATH="$project/plugin${OCAMLPATH:+:$OCAMLPATH}"
make -C "$project" -j1 evaluate/RocqOfRust.vo lib/simulate/lib.vo core/char/methods.vo core/slice/simulate/mod.vo
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
flags=(-R "$project" RocqOfRust -I "$project/plugin" -impredicative-set -Q "$work" ReleaseTests)
for source in *.rs; do
  name=${source%.rs}
  rustc -C overflow-checks=off "$source" -o "$work/native"
  "$work/native"
  "$translator" translate --path "$source" --output-path "$work"
  coqc "${flags[@]}" "$work/$name.v"
  cp "${name}_check.v" "$work/"
  coqc "${flags[@]}" "$work/${name}_check.v"
done
cp core_char.v "$work/"
coqc "${flags[@]}" "$work/core_char.v"
python3 exhaustive_division.py
