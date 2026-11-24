Require Import RocqOfRust.links.RocqOfRust.
Require Import RocqOfRust.lib.simulate.lib.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlZInt.
Definition pair_checked (a b : Z) : (option Z * option Z)%type :=
  let x : Integer.t IntegerKind.I8 := {| Integer.value := a |} in
  let y : Integer.t IntegerKind.I8 := {| Integer.value := b |} in
  (option_map (@Integer.value IntegerKind.I8) (BinOp.Checked.div x y),
   option_map (@Integer.value IntegerKind.I8) (BinOp.Checked.rem x y)).
Extraction "extracted.ml" pair_checked.
