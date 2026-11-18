Require Import simulate.RocqOfRust.
From Stdlib Require Import List.
Require Import alloy_primitives.bits.links.address.
Require Import revm.revm_state.simulate.lib.
Require Import alloy_primitives.links.aliases.
Require Import ruint.links.lib.

Import ListNotations.

(** Executable maps for types.rs. [update] represents access through get_mut:
    missing entries are invariant failures, never newly created accounts. *)
Module EvmState.
  Definition t := list (Address.t * Account.t).

  Fixpoint get (address : Address.t) (state : t) : option Account.t :=
    match state with
    | [] => None
    | (key, account) :: rest =>
      if Z.eqb address.(Address.value) key.(Address.value) then Some account
      else get address rest
    end.

  Fixpoint insert (address : Address.t) (account : Account.t) (state : t) : t :=
    match state with
    | [] => [(address, account)]
    | (key, value) :: rest =>
      if Z.eqb address.(Address.value) key.(Address.value) then (key, account) :: rest
      else (key, value) :: insert address account rest
    end.

  Fixpoint update (address : Address.t) (f : Account.t -> Account.t) (state : t) : option t :=
    match state with
    | [] => None
    | (key, account) :: rest =>
      if Z.eqb address.(Address.value) key.(Address.value) then Some ((key, f account) :: rest)
      else option_map (cons (key, account)) (update address f rest)
    end.
End EvmState.

Module EvmStorage.
  Definition t := list (aliases.U256.t * EvmStorageSlot.t).

  Fixpoint get (key : aliases.U256.t) (storage : t) : option EvmStorageSlot.t :=
    match storage with
    | [] => None
    | (slot_key, slot) :: rest =>
      if Z.eqb key.(Uint.value) slot_key.(Uint.value) then Some slot else get key rest
    end.

  Fixpoint insert (key : aliases.U256.t) (slot : EvmStorageSlot.t) (storage : t) : t :=
    match storage with
    | [] => [(key, slot)]
    | (slot_key, value) :: rest =>
      if Z.eqb key.(Uint.value) slot_key.(Uint.value) then (slot_key, slot) :: rest
      else (slot_key, value) :: insert key slot rest
    end.

  Fixpoint update (key : aliases.U256.t) (f : EvmStorageSlot.t -> EvmStorageSlot.t)
      (storage : t) : option t :=
    match storage with
    | [] => None
    | (slot_key, slot) :: rest =>
      if Z.eqb key.(Uint.value) slot_key.(Uint.value) then Some ((slot_key, f slot) :: rest)
      else option_map (cons (slot_key, slot)) (update key f rest)
    end.
End EvmStorage.

Module TransientStorage.
  Definition t := list ((Address.t * aliases.U256.t) * aliases.U256.t).

  Definition key_eq (x y : Address.t * aliases.U256.t) : bool :=
    Z.eqb (fst x).(Address.value) (fst y).(Address.value) &&
      Z.eqb (snd x).(Uint.value) (snd y).(Uint.value).

  Fixpoint get (key : Address.t * aliases.U256.t) (storage : t) : option aliases.U256.t :=
    match storage with
    | [] => None
    | (slot_key, value) :: rest =>
      if key_eq key slot_key then Some value else get key rest
    end.

  Fixpoint insert (key : Address.t * aliases.U256.t) (value : aliases.U256.t) (storage : t) : t :=
    match storage with
    | [] => [(key, value)]
    | (slot_key, old) :: rest =>
      if key_eq key slot_key then (slot_key, value) :: rest
      else (slot_key, old) :: insert key value rest
    end.

  Fixpoint remove (key : Address.t * aliases.U256.t) (storage : t) : t :=
    match storage with
    | [] => []
    | (slot_key, value) :: rest =>
      if key_eq key slot_key then rest else (slot_key, value) :: remove key rest
    end.
End TransientStorage.
