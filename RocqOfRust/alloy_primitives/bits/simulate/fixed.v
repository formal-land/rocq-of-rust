Require Import simulate.RocqOfRust.
Require Export alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.links.aliases.
Require Import core.convert.simulate.mod.
Require Import core.links.array.
Require Import ruint.links.lib.

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

Module Impl_FixedBytes.
  Definition Self (N : usize) : Set :=
    FixedBytes.t N.

  Definition ZERO {N : usize} : Self N :=
    {| FixedBytes.value := {|
      array.value := ArrayPairs.repeat (0 : u8) (Z.to_nat i[N])
    |} |}.

  Lemma ZERO_eq
      (stack : Stack.t)
      (N : usize) :
    {{
      SimulateM.eval_f
        (Impl_FixedBytes.run_zero N)
        stack 🌲
      (
        Output.Success (Ref.immediate Pointer.Kind.Raw ZERO),
        stack
      )
    }}.
  Proof.
  Admitted.

  Definition new {N : usize} (bytes : array.t u8 N) : Self N :=
    {| FixedBytes.value := bytes |}.

  Lemma new_eq
      (stack : Stack.t)
      (N : usize)
      (bytes : array.t u8 N) :
    {{
      SimulateM.eval_f
        (Impl_FixedBytes.run_new N bytes)
        stack 🌲
      (
        Output.Success (new bytes),
        stack
      )
    }}.
  Proof.
  Admitted.
End Impl_FixedBytes.

Module Impl_From_FixedBytes_32_for_U256.
  Definition Self : Set :=
    aliases.U256.t.

  Definition from (value : FixedBytes.t {| Integer.value := 32 |}) : Self :=
    {| Uint.value := FixedBytes.to_Z value |}.

  Lemma from_eq (value : FixedBytes.t {| Integer.value := 32 |}) (stack : Stack.t) :
    {{
      SimulateM.eval_f
        (Impl_From_FixedBytes_32_for_U256.run_from value)
        stack 🌲
      (Output.Success (from value), stack)
    }}.
  Proof.
  Admitted.

  Instance I : From.C Self (FixedBytes.t {| Integer.value := 32 |}) := {|
    From.from := from;
  |}.

  Module Eq.
    Instance I : From.Eq.C (Self := Self) (T := FixedBytes.t {| Integer.value := 32 |}) I.
    Proof.
      constructor.
      apply from_eq.
    Qed.
  End Eq.
  Export (hints) Eq.
End Impl_From_FixedBytes_32_for_U256.
Export (hints) Impl_From_FixedBytes_32_for_U256.

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
  Proof.
  Admitted.

  Instance I : From.C Self aliases.U256.t := {|
    From.from := from;
  |}.

  Module Eq.
    Instance I : From.Eq.C (Self := Self) (T := aliases.U256.t) I.
    Proof.
      constructor.
      apply from_eq.
    Qed.
  End Eq.
  Export (hints) Eq.
End Impl_From_U256_for_FixedBytes_32.
Export (hints) Impl_From_U256_for_FixedBytes_32.
