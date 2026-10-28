Require Import simulate.RocqOfRust.
Require Import core.links.result.
Require Import revm.revm_context.journal.simulate.inner.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.journaled_state.
Require Import revm.revm_database_interface.simulate.lib.
Require Import revm.revm_state.simulate.lib.
Require Import alloy_primitives.bits.links.address.

(** A successful code load always fills AccountInfo.code, including empty code. *)
Lemma load_code_present {DB Error : Set} `{Database.C DB Error}
    (self : JournalInner.t) (db : DB) (address : Address.t) (skip : bool) :
  let '(result, _, _) := Impl_JournalInner.load_account_optional self db address true skip in
  match result with
  | Result.Err _ => True
  | Result.Ok (account, _) => exists code, account.(Account.info).(AccountInfo.code) = Some code
  end.
Proof.
  unfold Impl_JournalInner.load_account_optional.
  cbn beta iota zeta.
  repeat first [solve [eauto] | solve [eexists; reflexivity] |
    progress cbn beta iota zeta delta [Account.info AccountInfo.code] |
    match goal with
    | |- context [types.EvmState.get ?address ?state] => destruct (types.EvmState.get address state) eqn:?
    | |- context [if ?condition then _ else _] => destruct condition eqn:?
    | |- context [Impl_Account.mark_warm_with_transaction_id ?account ?id] => destruct (Impl_Account.mark_warm_with_transaction_id account id) eqn:?
    | |- context [Database.basic ?db ?address] => destruct (Database.basic db address) as [[] ?] eqn:?
    | |- context [Database.code_by_hash ?db ?hash] => destruct (Database.code_by_hash db hash) as [[] ?] eqn:?
    | |- context [match AccountInfo.code ?info with _ => _ end] => destruct (AccountInfo.code info) eqn:?
    | |- context [match ?info with Some _ => _ | None => _ end] => is_var info; destruct info eqn:?
    end].
Qed.
