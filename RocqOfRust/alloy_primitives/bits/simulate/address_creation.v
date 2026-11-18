Require Import simulate.RocqOfRust.
From Stdlib Require Import List.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import core.links.array.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.utils.simulate.keccak256.

Module Impl_AddressCreation.
  Definition Self : Set := Address.t.

  (** RLP nonce encoding: the input is bounded by Rust's u64 type, so the
      fixed buffer has eight bytes. No unbounded unary length conversion. *)
  Fixpoint trim_zero_bytes (bytes : list u8) : list u8 :=
    match bytes with
    | [] => []
    | byte :: rest => if Z.eqb byte.(Integer.value) 0 then trim_zero_bytes rest else bytes
    end.

  Definition encode_nonce (nonce : u64) : list u8 :=
    if Z.eqb nonce.(Integer.value) 0 then [(128 : u8)] else
    if Z.ltb nonce.(Integer.value) 128 then [{| Integer.value := nonce.(Integer.value) |}] else
    let bytes := trim_zero_bytes (ArrayPairs.to_list
      (FixedBytes.from_Z (N := 8) nonce.(Integer.value)).(FixedBytes.value).(array.value)) in
    {| Integer.value := 128 + Z.of_nat (List.length bytes) |} :: bytes.

  Definition hash_address (bytes : list u8) : Address.t :=
    {| Address.value := List.fold_left (fun acc byte => 256 * acc + byte)%Z
        (List.skipn 12 (Keccak256.hash (List.map Integer.value bytes))) 0%Z |}.

  Definition create (self : Self) (nonce : u64) : Self :=
    let address := ArrayPairs.to_list
      (FixedBytes.from_Z (N := 20) self.(Address.value)).(FixedBytes.value).(array.value) in
    let nonce := encode_nonce nonce in
    let payload := (148 : u8) :: address ++ nonce in
    hash_address ({| Integer.value := 192 + Z.of_nat (List.length payload) |} :: payload).

  Definition create2 (self : Self) (salt init_code_hash : aliases.B256.t) : Self :=
    let address := ArrayPairs.to_list
      (FixedBytes.from_Z (N := 20) self.(Address.value)).(FixedBytes.value).(array.value) in
    hash_address ((255 : u8) :: address ++
      ArrayPairs.to_list salt.(FixedBytes.value).(array.value) ++
      ArrayPairs.to_list init_code_hash.(FixedBytes.value).(array.value)).
End Impl_AddressCreation.
