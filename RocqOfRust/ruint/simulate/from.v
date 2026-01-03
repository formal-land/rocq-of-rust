Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import core.links.result.
Require Import ruint.links.from.
Require Import ruint.links.lib.
Require Import ruint.simulate.lib.

Module UintTryFrom.
  Class C (Self T : Set) : Set := {
    uint_try_from (value : T) : Result.t Self (ToUintError.t Self);
  }.

  Module Eq.
    Class C (Self T : Set) `{Link Self} `{Link T} `{C Self T} `{!UintTryFrom.Run Self T} : Set := {
      uint_try_from_eq (value : T) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (UintTryFrom.run_uint_try_from.(TraitMethod.run) value)
            stack 🌲
          (
            Output.Success (uint_try_from value),
            stack
          )
        }};
    }.
  End Eq.
End UintTryFrom.

Module Impl_Uint.
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  Definition from {BITS LIMBS : Usize.t} {T : Set} `{UintTryFrom.C (Self BITS LIMBS) T}
      (value : T) :
      Self BITS LIMBS :=
    match UintTryFrom.uint_try_from value with
    | Result.Ok n => n
    | Result.Err e => Impl_Uint.ZERO
    end.

  Lemma from_eq (BITS LIMBS : Usize.t) (T : Set) `{Link T}
      `{UintTryFrom.C (Self BITS LIMBS) T}
      `{!UintTryFrom.Run (Self BITS LIMBS) T}
      `{!UintTryFrom.Eq.C (Self BITS LIMBS) T}
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
    (* eapply Run.Call. {
      apply UintTryFrom.Eq.uint_try_from_eq.
    }
    destruct (_.(UintTryFrom.uint_try_from) value) as [n |]; cbn.
    { apply Run.Pure. }
    { easy. } *)
  Admitted.
End Impl_Uint.

Module TryFrom_Uint_for_u64.
  Definition Self : Set :=
    U64.t.

  Parameter try_from :
    forall {BITS LIMBS : Usize.t},
    Impl_Uint.Self BITS LIMBS ->
    Result.t Self (FromUintError.t U64.t).

  Lemma try_from_eq (BITS LIMBS : Usize.t) (value : Impl_Uint.Self BITS LIMBS) (stack : Stack.t) :
    {{
      SimulateM.eval_f
        (TryFrom_Uint_for_u64.run_try_from BITS LIMBS value)
        stack 🌲
      (
        Output.Success (try_from value),
        stack
      )
    }}.
  Admitted.
End TryFrom_Uint_for_u64.
