Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.simulate.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import core.convert.simulate.mod.
Require Import revm.revm_interpreter.instructions.links.utility.
Require Import ruint.links.lib.

Definition cast_slice_to_u256 (slice : list u8) : aliases.U256.t :=
  {|
    Uint.value := List.fold_left (fun acc byte => (acc * 256) + i[byte])%Z slice 0;
  |}.

Lemma cast_slice_to_address_like
    (stack : Stack.t)
    (slice : '& (list u8))
    (dest : '&mut aliases.U256.t) :
  SimulateM.eval_f
    (run_cast_slice_to_u256 slice dest)
    stack =
  let*s slice := SimulateM.read stack slice.(Ref.core) in
  match slice with
  | Output.Success slice =>
    let*s stack' := SimulateM.write stack dest.(Ref.core) (cast_slice_to_u256 slice) in
    match stack' with
    | Output.Success stack' =>
      SimulateM.Pure (Output.Success tt, stack')
    | Output.Exception exception =>
      SimulateM.Pure (Output.Exception exception, stack)
    end
  | Output.Exception exception =>
    SimulateM.Pure (Output.Exception exception, stack)
  end.
Admitted.

Module IntoU256.
  Class C (Self : Set) : Set := {
    into_u256 (self : Self) : aliases.U256.t;
  }.

  Module Eq.
    Class C
        {Self : Set} `{Link Self}
        `{!utility.IntoU256.Run Self}
        `(!IntoU256.C Self) :
        Prop := {
      into_u256 (self : Self) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (utility.IntoU256.run_into_u256 self)
            stack 🌲
          (
            Output.Success (into_u256 self),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End IntoU256.
Export (hints) IntoU256.

Module Impl_IntoU256_for_B256.
  Definition Self : Set :=
    aliases.B256.t.

  Definition into_u256 (self : Self) : aliases.U256.t :=
    Impl_From_FixedBytes_32_for_U256.from self.

  Lemma into_u256_eq (self : Self) (stack : Stack.t) :
    {{
      SimulateM.eval_f
        (utility.Impl_IntoU256_for_B256.run_into_u256 self)
        stack 🌲
      (Output.Success (into_u256 self), stack)
    }}.
  Admitted.

  Instance I : IntoU256.C Self := {|
    IntoU256.into_u256 := into_u256;
  |}.

  Module Eq.
    Instance I : IntoU256.Eq.C (Self := Self) Impl_IntoU256_for_B256.I.
    Proof.
      constructor.
      apply into_u256_eq.
    Qed.
  End Eq.
  Export (hints) Eq.
End Impl_IntoU256_for_B256.
Export (hints) Impl_IntoU256_for_B256.

Module Impl_IntoU256_for_Address.
  Definition Self : Set :=
    Address.t.

  Definition into_u256 (self : Self) : aliases.U256.t :=
    Impl_From_FixedBytes_32_for_U256.from (Impl_Address.into_word self).

  Lemma into_u256_eq (self : Self) (stack : Stack.t) :
    {{
      SimulateM.eval_f
        (utility.Impl_IntoU256_for_Address.run_into_u256 self)
        stack 🌲
      (Output.Success (into_u256 self), stack)
    }}.
  Admitted.

  Instance I : IntoU256.C Self := {|
    IntoU256.into_u256 := into_u256;
  |}.

  Module Eq.
    Instance I : IntoU256.Eq.C (Self := Self) Impl_IntoU256_for_Address.I.
    Proof.
      constructor.
      apply into_u256_eq.
    Qed.
  End Eq.
  Export (hints) Eq.
End Impl_IntoU256_for_Address.
Export (hints) Impl_IntoU256_for_Address.

Module IntoAddress.
  Class C (Self : Set) : Set := {
    into_address (self : Self) : Address.t;
  }.

  Module Eq.
    Class C
        {Self : Set} `{Link Self}
        `{!utility.IntoAddress.Run Self}
        `(!IntoAddress.C Self) :
        Prop := {
      into_address (self : Self) (stack : Stack.t) :
        {{
          SimulateM.eval_f
            (utility.IntoAddress.run_into_address self)
            stack 🌲
          (
            Output.Success (into_address self),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End IntoAddress.
Export (hints) IntoAddress.

Module Impl_IntoAddress_for_U256.
  Definition into_address (self : aliases.U256.t) : Address.t :=
    Impl_Address.from_word (Impl_From_U256_for_FixedBytes_32.from self).

  Lemma into_address_eq (self : aliases.U256.t) (stack : Stack.t) :
    {{
      SimulateM.eval_f
        (Impl_IntoAddress_for_U256.run_into_address self)
        stack 🌲
      (Output.Success (into_address self), stack)
    }}.
  Proof.
  Admitted.

  Instance I : IntoAddress.C aliases.U256.t := {|
    IntoAddress.into_address := into_address;
  |}.

  Module Eq.
    Instance I : IntoAddress.Eq.C (Self := aliases.U256.t) Impl_IntoAddress_for_U256.I.
    Proof.
      constructor.
      apply into_address_eq.
    Qed.
  End Eq.
  Export (hints) Eq.
End Impl_IntoAddress_for_U256.
Export (hints) Impl_IntoAddress_for_U256.
