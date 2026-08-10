Require Import simulate.RocqOfRust.
Require Import core.links.array.
Require Import core.links.option.
Require Import ruint.links.lib.
Require Import ruint.links.bytes.

Module Impl_Uint.
  Definition Self : Set := Uint.t 256 4.

  Definition to_be_bytes (self : Self) : array.t u8 32 :=
    let v := self.(Uint.value) in
    {|
      array.value := ArrayPairs.of_list [
        (v / 2^248) mod 256 : u8;
        (v / 2^240) mod 256 : u8;
        (v / 2^232) mod 256 : u8;
        (v / 2^224) mod 256 : u8;
        (v / 2^216) mod 256 : u8;
        (v / 2^208) mod 256 : u8;
        (v / 2^200) mod 256 : u8;
        (v / 2^192) mod 256 : u8;
        (v / 2^184) mod 256 : u8;
        (v / 2^176) mod 256 : u8;
        (v / 2^168) mod 256 : u8;
        (v / 2^160) mod 256 : u8;
        (v / 2^152) mod 256 : u8;
        (v / 2^144) mod 256 : u8;
        (v / 2^136) mod 256 : u8;
        (v / 2^128) mod 256 : u8;
        (v / 2^120) mod 256 : u8;
        (v / 2^112) mod 256 : u8;
        (v / 2^104) mod 256 : u8;
        (v / 2^96) mod 256 : u8;
        (v / 2^88) mod 256 : u8;
        (v / 2^80) mod 256 : u8;
        (v / 2^72) mod 256 : u8;
        (v / 2^64) mod 256 : u8;
        (v / 2^56) mod 256 : u8;
        (v / 2^48) mod 256 : u8;
        (v / 2^40) mod 256 : u8;
        (v / 2^32) mod 256 : u8;
        (v / 2^24) mod 256 : u8;
        (v / 2^16) mod 256 : u8;
        (v / 2^8) mod 256 : u8;
        v mod 256 : u8
      ] : ArrayPairs.t _ (Z.to_nat (i[32]));
    |}.

  Lemma to_be_bytes_eq
      (stack : Stack.t)
      (ref_self : '& Self)
      (self : Self) :
    CanRead.t stack self ref_self ->
    {{
      SimulateM.eval_f
        (Impl_Uint.run_to_be_bytes 256 4 32 ref_self)
        stack 🌲
      (
        Output.Success (to_be_bytes self),
        stack
      )
    }}.
  Proof.
  Admitted.

  Fixpoint bytes_to_value_aux (bytes : list u8) (acc : Z) : Z :=
    match bytes with
    | [] => acc
    | b :: rest => bytes_to_value_aux rest (acc * 256 + b.(Integer.value))
    end.

  Definition bytes_to_value (bytes : list u8) : Z :=
    bytes_to_value_aux bytes 0.

  Definition from_be_bytes (bytes : array.t u8 32) : Self :=
    {| Uint.value := bytes_to_value (ArrayPairs.to_list bytes.(array.value)) |}.

  Lemma from_be_bytes_eq
      (stack : Stack.t)
      (bytes : array.t u8 32) :
    {{
      SimulateM.eval_f
        (Impl_Uint.run_from_be_bytes 256 4 32 bytes)
        stack 🌲
      (
        Output.Success (from_be_bytes bytes),
        stack
      )
    }}.
  Proof.
  Admitted.

  Definition try_from_be_slice (bytes : list u8) : option Self :=
    if Nat.eqb (List.length bytes) 32 then
      Some {| Uint.value := bytes_to_value bytes |}
    else
      None.

  Lemma try_from_be_slice_eq
      (stack : Stack.t)
      (ref_bytes : '& (list u8))
      (bytes : list u8) :
    CanRead.t stack bytes ref_bytes ->
    {{
      SimulateM.eval_f
        (Impl_Uint.run_try_from_be_slice 256 4 ref_bytes)
        stack 🌲
      (
        Output.Success (try_from_be_slice bytes),
        stack
      )
    }}.
  Proof.
  Admitted.
End Impl_Uint.
