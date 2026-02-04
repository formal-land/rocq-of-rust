Require Import simulate.RocqOfRust.
Require Import core.convert.links.mod.
Require Import core.convert.simulate.mod.
Require Import core.links.result.
Require Import ruint.links.from.
Require Import ruint.links.lib.
Require Import ruint.simulate.lib.

Module UintTryFrom.
  Class C (Self T : Set) : Set := {
    uint_try_from (value : T) : Result.t Self (ToUintError.t Self);
  }.

  Module Eq.
    Class C {Self T : Set} `{Link Self} `{Link T}
        `{run : !UintTryFrom.Run Self T}
        `(!C Self T) :
        Prop := {
      uint_try_from_eq (value : T) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (UintTryFrom.run_uint_try_from value)
            stack 🌲
          (
            Output.Success (uint_try_from value),
            stack
          )
        }};
    }.
  End Eq.
End UintTryFrom.

Module UintTryFrom_T_for_Uint_where_TryFrom.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  Definition uint_try_from {BITS LIMBS : usize} {T : Set}
      `{!TryFrom.C (Self BITS LIMBS) T (ToUintError.t (Self BITS LIMBS))}
      (value : T) :
    Result.t (Self BITS LIMBS) (ToUintError.t (Self BITS LIMBS)) :=
    TryFrom.try_from value.

  Lemma uint_try_from_eq {BITS LIMBS : usize} {T : Set} `{Link T}
      `{!TryFrom.Run (Self BITS LIMBS) T (ToUintError.t (Self BITS LIMBS))}
      `{I : !TryFrom.C (Self BITS LIMBS) T (ToUintError.t (Self BITS LIMBS))}
      `{H_TryFrom : !TryFrom.Eq.C I}
      (value : T) (stack : Stack.t) :
    {{
      SimulateM.eval_f
        (UintTryFrom_T_for_Uint_where_TryFrom.run_uint_try_from value)
        stack 🌲
      (
        Output.Success (uint_try_from value),
        stack
      )
    }}.
  Proof.
    eapply Run.Call. {
      apply H_TryFrom.
    }
    apply Run.Pure.
  Qed.

  Instance I {BITS LIMBS : usize} {T : Set} `{Link T}
      `(!TryFrom.C (Self BITS LIMBS) T (ToUintError.t (Self BITS LIMBS))) :
    UintTryFrom.C (Self BITS LIMBS) T := {
      uint_try_from := uint_try_from;
    }.

  Module Eq.
    Instance I {BITS LIMBS : usize} {T : Set} `{Link T}
      `{!TryFrom.Run (Self BITS LIMBS) T (ToUintError.t (Self BITS LIMBS))}
      `{I_TryFrom : !TryFrom.C (Self BITS LIMBS) T (ToUintError.t (Self BITS LIMBS))}
      `{!TryFrom.Eq.C I_TryFrom} :
      UintTryFrom.Eq.C (I I_TryFrom) := {
      uint_try_from_eq := uint_try_from_eq;
    }.
  End Eq.
  Export (hints) Eq.
End UintTryFrom_T_for_Uint_where_TryFrom.
Export (hints) UintTryFrom_T_for_Uint_where_TryFrom.

Module Impl_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  Definition from {BITS LIMBS : usize} {T : Set} `{!UintTryFrom.C (Self BITS LIMBS) T}
      (value : T) :
      Self BITS LIMBS :=
    match UintTryFrom.uint_try_from value with
    | Result.Ok n => n
    | Result.Err e => Impl_Uint.ZERO
    end.

  Lemma from_eq (BITS LIMBS : usize) (T : Set) `{Link T}
      `{I_TryFrom : !UintTryFrom.C (Self BITS LIMBS) T}
      `{!UintTryFrom.Run (Self BITS LIMBS) T}
      `{H_TryFrom : !UintTryFrom.Eq.C I_TryFrom}
      (value : T) (stack : Stack.t)
      (H_success :
        match UintTryFrom.uint_try_from value with
        | Result.Ok _ => True
        | Result.Err _ => False
        end
      ) :
    {{
      SimulateM.eval_f
        (Impl_Uint.run_from BITS LIMBS _ value)
        stack 🌲
      (
        Output.Success (from value),
        stack
      )
    }}.
  Proof.
    with_strategy transparent [Impl_Uint.run_from] cbn.
    unfold from.
    eapply Run.Call. {
      apply H_TryFrom.
    }
    cbn.
    destruct (I_TryFrom.(UintTryFrom.uint_try_from) value) as [n|e]; cbn.
    { apply Run.Pure. }
    { easy. }
  Qed.
End Impl_Uint.

Module TryFrom_bool_for_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  Definition Error (BITS LIMBS : usize) : Set :=
    ToUintError.t (Self BITS LIMBS).

  Definition try_from {BITS LIMBS : usize} (value : bool) :
      Result.t (Self BITS LIMBS) (Error BITS LIMBS) :=
    Result.Ok match value with
    | true => {| Uint.value := 1 |}
    | false => {| Uint.value := 0 |}
  end.

  Lemma try_from_eq {BITS LIMBS : usize} (value : bool) (stack : Stack.t) :
    {{
      SimulateM.eval_f
        (TryFrom_bool_for_Uint.run_try_from BITS LIMBS value)
        stack 🌲
      (
        Output.Success (try_from value),
        stack
      )
    }}.
  Proof.
  Admitted.

  Instance I (BITS LIMBS : usize) : TryFrom.C (Self BITS LIMBS) bool (Error BITS LIMBS) := {
    try_from := try_from;
  }.

  Module Eq.
    Instance I {BITS LIMBS : usize} : TryFrom.Eq.C (I BITS LIMBS) := {
      try_from := try_from_eq;
    }.
  End Eq.
  Export (hints) Eq.
End TryFrom_bool_for_Uint.
Export (hints) TryFrom_bool_for_Uint.

Module TryFrom_u8_for_Uint.
  Definition Self (BITS LIMBS : usize) : Set :=
    Uint.t BITS LIMBS.

  Definition Error (BITS LIMBS : usize) : Set :=
    ToUintError.t (Self BITS LIMBS).

  Definition try_from {BITS LIMBS : usize} (value : u8) :
      Result.t (Self BITS LIMBS) (Error BITS LIMBS) :=
    Result.Ok {| Uint.value := i[value] |}.

  Lemma try_from_eq {BITS LIMBS : usize} (value : u8) (stack : Stack.t) :
    {{
      SimulateM.eval_f
        (TryFrom_u8_for_Uint.run_try_from BITS LIMBS value)
        stack 🌲
      (
        Output.Success (try_from value),
        stack
      )
    }}.
  Proof.
  Admitted.

  Instance I (BITS LIMBS : usize) : TryFrom.C (Self BITS LIMBS) u8 (Error BITS LIMBS) := {
    try_from := try_from;
  }.

  Module Eq.
    Instance I {BITS LIMBS : usize} : TryFrom.Eq.C (I BITS LIMBS) := {
      try_from := try_from_eq;
    }.
  End Eq.
  Export (hints) Eq.
End TryFrom_u8_for_Uint.
Export (hints) TryFrom_u8_for_Uint.

Module TryFrom_Uint_for_u64.
  Definition Self : Set :=
    u64.

  Definition Error : Set :=
    FromUintError.t u64.

  (** We specialize the definition for the case of BITS = 256 and LIMBS = 4. *)
  Definition try_from (value : Impl_Uint.Self 256 4) : Result.t Self Error :=
    if value.(Uint.value) <=? 2^64 - 1 then
      Result.Ok (value.(Uint.value) : u64)
    else
      Result.Err (FromUintError.Overflow 256 (value.(Uint.value) mod (2^64): u64) (2^64 - 1)).

  Lemma try_from_eq (value : Impl_Uint.Self 256 4) (stack : Stack.t) :
    {{
      SimulateM.eval_f
        (TryFrom_Uint_for_u64.run_try_from 256 4 value)
        stack 🌲
      (
        Output.Success (try_from value),
        stack
      )
    }}.
  Admitted.
End TryFrom_Uint_for_u64.
