Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import core.links.array.
Require Import examples.default.examples.custom.loops_free.
Require Import core.links.array.

Instance run_max2 (a b : U32.t) : Run.Trait max2 [] [] [φ a; φ b] U32.t.
Proof.
  constructor.
  run_symbolic.
Defined.

Instance run_abs_i32 (x : I32.t) : Run.Trait abs_i32 [] [] [φ x] I32.t.
Proof.
  constructor.
  run_symbolic.
Defined.

Instance run_bool_and (a b : bool) : Run.Trait bool_and [] [] [φ a; φ b] bool.
Proof.
  constructor.
  run_symbolic.
Defined.

(* pub fn get_or_zero(xs: &[u32; 4], i: usize) -> u32 *)
Instance run_get_or_zero
    (xs : Ref.t Pointer.Kind.Ref (array.t U32.t {| Integer.value := 4 |}))
    (i : Usize.t) :
  Run.Trait get_or_zero [] [] [φ xs; φ i] U32.t.
Proof.
  constructor.
  run_symbolic.
Defined.

(* pub fn eq2(a: &[u32; 2], b: &[u32; 2]) -> bool *)
Instance run_eq2
    (a : Ref.t Pointer.Kind.Ref (array.t U32.t {| Integer.value := 2 |}))
    (b : Ref.t Pointer.Kind.Ref (array.t U32.t {| Integer.value := 2 |})) :
  Run.Trait eq2 [] [] [φ a; φ b] bool.
Proof.
  constructor.
  run_symbolic.
Defined.

(* pub fn eq_pair(x: (u32, u32), y: (u32, u32)) -> bool *)
Instance run_eq_pair
    (x : U32.t * U32.t)
    (y : U32.t * U32.t) :
  Run.Trait eq_pair [] [] [φ x; φ y] bool.
Proof.
  constructor.
  run_symbolic.
Defined.

(* pub fn min3(a: u32, b: u32, c: u32) -> u32 *)
Instance run_min3 (a b c : U32.t) : Run.Trait min3 [] [] [φ a; φ b; φ c] U32.t.
Proof.
  constructor.
  run_symbolic.
Defined.

(* pub fn choose_ref<'a>(choice: bool, a: &'a u32, b: &'a u32) -> &'a u32 *)
Instance run_choose_ref (choice : bool) (a b : Ref.t Pointer.Kind.Ref U32.t) :
  Run.Trait choose_ref [] [] [φ choice; φ a; φ b] U32.t.
Proof.
  constructor.
  run_symbolic.
Defined.
