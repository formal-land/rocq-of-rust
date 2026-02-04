Require Import simulate.RocqOfRust.
Require Export alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.

Module FixedBytes.
  (** Convert to [Z] interpreting in big-endian. *)
  Definition to_Z {N : usize} (x : FixedBytes.t N) : Z :=
    let bytes := ArrayPairs.to_list x.(FixedBytes.value).(array.value) in
    List.fold_left (fun acc byte => 256 * acc + i[byte] : Z) bytes 0.

  (** Generate n bytes in big-endian order directly as ArrayPairs. *)
  Fixpoint bytes_be (n : nat) (value : Z) : ArrayPairs.t u8 n :=
    match n return ArrayPairs.t u8 n with
    | O => ArrayEmpty.Make
    | S n' =>
      let shift := (Z.of_nat n' * 8)%Z in
      {| ArrayPair.x := {| Integer.value := (value / 2 ^ shift) mod 256 |};
         ArrayPair.xs := bytes_be n' value |}
    end.

  (** Convert from [Z] interpreting in big-endian. *)
  Definition from_Z {N : usize} (value : Z) : FixedBytes.t N :=
    let n := Z.to_nat N.(Integer.value) in
    {| FixedBytes.value := {| array.value := bytes_be n value |} |}.
End FixedBytes.

Module Impl_From_U256_for_FixedBytes_32.
  Definition Self : Set :=
    FixedBytes.t {| Integer.value := 32 |}.

  Definition from (value : aliases.U256.t) : Self :=
    FixedBytes.from_Z value.(lib.Uint.value).

  Lemma from_eq (value : aliases.U256.t) (stack : Stack.t) :
    {{
      SimulateM.eval_f
        (Impl_From_U256_for_FixedBytes_32.run_from value)
        stack 🌲
      (
        Output.Success (from value),
        stack
      )
    }}.
  Admitted.
End Impl_From_U256_for_FixedBytes_32.
