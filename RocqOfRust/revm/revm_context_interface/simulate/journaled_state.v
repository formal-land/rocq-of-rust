Require Import simulate.RocqOfRust.
Require Import core.ops.links.deref.
Require Import core.ops.simulate.deref.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import ruint.links.lib.

Module Impl_Deref_for_StateLoad.
  Definition Self (T : Set) `{Link T} : Set :=
    StateLoad.t T.

  Definition deref {T : Set} `{Link T} : RefStub.t (Self T) T := {|
    RefStub.path := [];
    RefStub.projection x := x.(StateLoad.data);
    RefStub.injection x y := x <| StateLoad.data := y |>;
  |}.

  Lemma deref_eq
      {T : Set} `{Link T}
      (ref_self : '& (Self T))
      (self : Self T)
      (stack : Stack.t) :
    CanRead.t stack self ref_self ->
    {{
      SimulateM.eval_f
        (Deref.run_deref ref_self)
        stack 🌲
      (
        Output.Success (RefStub.apply ref_self deref),
        stack
      )
    }}.
  Proof.
  Admitted.

  Instance I {T : Set} `{Link T} :
      core.ops.simulate.deref.Deref.C (Self T) T := {|
    core.ops.simulate.deref.Deref.deref := deref;
  |}.

  Module Eq.
    Instance I {T : Set} `{Link T} :
      core.ops.simulate.deref.Deref.Eq.t
        (Self := Self T) (Target := T) Impl_Deref_for_StateLoad.I.
    Proof.
    Admitted.
  End Eq.
  Export (hints) Eq.
End Impl_Deref_for_StateLoad.
Export (hints) Impl_Deref_for_StateLoad.

Module Impl_Eip7702CodeLoad.
  Definition Self (T : Set) `{Link T} : Set :=
    Eip7702CodeLoad.t T.

  Definition into_components {T : Set} `{Link T} (self : Self T) : T * Self unit :=
    (
      self.(Eip7702CodeLoad.state_load).(StateLoad.data),
      {|
        Eip7702CodeLoad.state_load := {|
          StateLoad.data := tt;
          StateLoad.is_cold :=
            self.(Eip7702CodeLoad.state_load).(StateLoad.is_cold);
        |};
        Eip7702CodeLoad.is_delegate_account_cold :=
          self.(Eip7702CodeLoad.is_delegate_account_cold);
      |}
    ).

End Impl_Eip7702CodeLoad.
Export (hints) Impl_Eip7702CodeLoad.

Parameter abstract_account_info_load_original_bytes :
  AccountInfoLoad.t -> Bytes.t.

Definition account_info_load_original_bytes (load : AccountInfoLoad.t) : Bytes.t :=
  match load.(AccountInfoLoad.account) with
  | Cow.Owned account =>
      match account.(AccountInfo.code) with
      | Some code => code.(Bytecode.original_bytes)
      | None => abstract_account_info_load_original_bytes load
      end
  | Cow.Borrowed _ => abstract_account_info_load_original_bytes load
  end.

Parameter borrowed_account_is_empty : '& AccountInfo.t -> bool.

Definition account_info_load_is_empty (load : AccountInfoLoad.t) : bool :=
  match load.(AccountInfoLoad.account) with
  | Cow.Owned account =>
      let code_hash := FixedBytes.to_Z account.(AccountInfo.code_hash) in
      ((code_hash =? 0) ||
        (code_hash =? 89477152217924674838424037953991966239322087453347756267410168184682657981552)) &&
      (account.(AccountInfo.balance).(Uint.value) =? 0) &&
      (account.(AccountInfo.nonce).(Integer.value) =? 0)
  | Cow.Borrowed account => borrowed_account_is_empty account
  end.

Parameter borrowed_account_code_hash :
  '& AccountInfo.t -> aliases.B256.t.

Definition account_info_load_code_hash (load : AccountInfoLoad.t) : aliases.B256.t :=
  match load.(AccountInfoLoad.account) with
  | Cow.Owned account => account.(AccountInfo.code_hash)
  | Cow.Borrowed account => borrowed_account_code_hash account
  end.

Parameter borrowed_account_balance :
  '& AccountInfo.t -> aliases.U256.t.

Definition account_info_load_balance (load : AccountInfoLoad.t) : aliases.U256.t :=
  match load.(AccountInfoLoad.account) with
  | Cow.Owned account => account.(AccountInfo.balance)
  | Cow.Borrowed account => borrowed_account_balance account
  end.
