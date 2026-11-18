From Stdlib Require Import Bool List ZArith.

Require Import alloy_primitives.utils.simulate.keccak256.
Require Import revm.revm_handler.simulate.ethereum_rlp.
Require Import revm.revm_handler.simulate.eest_types.

Import ListNotations.
Open Scope Z_scope.

(** Executable allocation commitments adapted from the parent EestCommitment.v,
    trie/Encoding.v, trie/Node.v, trie/Hasher.v, trie/Trie.v and
    trie/SecureTrie.v. A fresh allocation trie needs insertion only. The input
    contains finalized accounts, so account deletion/touch decisions belong to
    the transaction handler and are never inferred here from zero balances. *)
Module EthereumCommitment.
  Module Trie.
    Module Node.
      Inductive t : Set :=
      | Empty
      | Branch (children : list t)
      | Short (key : list Z) (value : t)
      | Value (value : list Z).

      Fixpoint set_child (children : list t) (index : nat) (child : t) : list t :=
        match children, index with
        | [], _ => []
        | _ :: rest, O => child :: rest
        | head :: rest, S index => head :: set_child rest index child
        end.

      Definition empty_children : list t := List.repeat Empty 17.
    End Node.

    Fixpoint key_nibbles (key : list Z) : list Z :=
      match key with
      | [] => [16]
      | byte :: rest => byte / 16 :: byte mod 16 :: key_nibbles rest
      end.

    Definition has_terminator (key : list Z) : bool :=
      match key with [] => false | _ => List.last key 0 =? 16 end.

    Fixpoint pack_nibbles (key : list Z) : list Z :=
      match key with
      | high_nibble :: low_nibble :: rest => (16 * high_nibble + low_nibble) :: pack_nibbles rest
      | _ => []
      end.

    Definition compact_key (key : list Z) : list Z :=
      let terminal := has_terminator key in
      let key := if terminal then List.firstn (Nat.pred (List.length key)) key else key in
      let flag := if terminal then 32 else 0 in
      if Nat.odd (List.length key)
      then (flag + 16 + List.hd 0 key) :: pack_nibbles (List.tl key)
      else flag :: pack_nibbles key.

    Fixpoint prefix_length (left right : list Z) : nat :=
      match left, right with
      | x :: xs, y :: ys => if x =? y then S (prefix_length xs ys) else O
      | _, _ => O
      end.

    Definition short (key : list Z) (value : Node.t) : Node.t :=
      match key with [] => value | _ => Node.Short key value end.

    Fixpoint insert (bound : nat) (node : Node.t) (key : list Z)
        (value : Node.t) : option Node.t :=
      match key with
      | [] => Some value
      | nibble :: tail =>
        match bound with
        | O => None
        | S bound =>
          match node with
          | Node.Empty => Some (Node.Short key value)
          | Node.Short old_key old_value =>
            let prefix := prefix_length key old_key in
            if Nat.eqb prefix (List.length old_key) then
              option_map (Node.Short old_key)
                (insert bound old_value (List.skipn prefix key) value)
            else
              let old_index := Z.to_nat (List.nth prefix old_key 0) in
              let new_index := Z.to_nat (List.nth prefix key 0) in
              let children := Node.set_child Node.empty_children old_index
                (short (List.skipn (S prefix) old_key) old_value) in
              let children := Node.set_child children new_index
                (short (List.skipn (S prefix) key) value) in
              Some (short (List.firstn prefix key) (Node.Branch children))
          | Node.Branch children =>
            let index := Z.to_nat nibble in
            option_map (fun child => Node.Branch (Node.set_child children index child))
              (insert bound (List.nth index children Node.Empty) tail value)
          | Node.Value _ => None
          end
        end
      end.

    Definition child_reference (encoded : list Z) : list Z :=
      if Nat.ltb (List.length encoded) 32 then encoded
      else EthereumRlp.encode_bytes (Keccak256.hash encoded).

    Fixpoint encode_node (node : Node.t) : list Z :=
      match node with
      | Node.Empty => EthereumRlp.encode_bytes []
      | Node.Value value => EthereumRlp.encode_bytes value
      | Node.Short key value =>
        let encoded := encode_node value in
        EthereumRlp.encode_list [EthereumRlp.encode_bytes (compact_key key);
          if has_terminator key then encoded else child_reference encoded]
      | Node.Branch children =>
        let fix encode_children (children : list Node.t) : list (list Z) :=
          match children with
          | [] => []
          | child :: rest =>
            let encoded := encode_node child in
            let encoded := match child with
              | Node.Empty | Node.Value _ => encoded
              | _ => child_reference encoded
              end in
            encoded :: encode_children rest
          end in
        EthereumRlp.encode_list (encode_children children)
      end.

    Definition update (node : Node.t) (key value : list Z) : option Node.t :=
      let key := key_nibbles key in
      insert (S (List.length key)) node key (Node.Value value).

    Definition root (entries : list (list Z * list Z)) : option (list Z) :=
      option_map (fun node => Keccak256.hash (encode_node node))
        (List.fold_left (fun state entry =>
          match state with
          | None => None
          | Some node => update node (fst entry) (snd entry)
          end) entries (Some Node.Empty)).
  End Trie.

  Definition bounded (bits value : Z) : bool := (0 <=? value) && (value <? 2 ^ bits).

  Fixpoint distinct (keys : list Z) : bool :=
    match keys with
    | [] => true
    | key :: rest => negb (List.existsb (Z.eqb key) rest) && distinct rest
    end.

  Definition storage_valid (slots : list (Z * Z)) : bool :=
    List.forallb (fun slot => bounded 256 (fst slot) && bounded 256 (snd slot)) slots &&
    distinct (List.map fst slots).

  Definition storage_root (slots : list (Z * Z)) : option (list Z) :=
    if negb (storage_valid slots) then None else
    Trie.root (List.map (fun slot =>
      (Keccak256.hash (EthereumRlp.fixed_big_endian 32 (fst slot)),
       EthereumRlp.encode_uint (snd slot)))
      (List.filter (fun slot => negb (snd slot =? 0)) slots)).

  Definition account_valid (account : EestTypes.Account.t) : bool :=
    bounded 160 account.(EestTypes.Account.address) &&
    bounded 64 account.(EestTypes.Account.nonce) &&
    bounded 256 account.(EestTypes.Account.balance) &&
    List.forallb (bounded 8) account.(EestTypes.Account.code) &&
    storage_valid account.(EestTypes.Account.storage).

  Definition state_root (accounts : list EestTypes.Account.t) : option (list Z) :=
    if negb (List.forallb account_valid accounts &&
      distinct (List.map EestTypes.Account.address accounts)) then None else
    let fix collect (accounts : list EestTypes.Account.t) : option (list (list Z * list Z)) :=
      match accounts with
      | [] => Some []
      | account :: rest =>
        match storage_root account.(EestTypes.Account.storage), collect rest with
        | Some storage, Some rest =>
          Some ((Keccak256.hash (EthereumRlp.fixed_big_endian 20 account.(EestTypes.Account.address)),
            EthereumRlp.encode_list [
              EthereumRlp.encode_uint account.(EestTypes.Account.nonce);
              EthereumRlp.encode_uint account.(EestTypes.Account.balance);
              EthereumRlp.encode_bytes storage;
              EthereumRlp.encode_bytes (Keccak256.hash account.(EestTypes.Account.code))]) :: rest)
        | _, _ => None
        end
      end in
    match collect accounts with
    | Some entries => Trie.root entries
    | None => None
    end.

  Definition log_valid (log : EestTypes.EvmLog.t) : bool :=
    bounded 160 log.(EestTypes.EvmLog.address) &&
    (Z.of_nat (List.length log.(EestTypes.EvmLog.topics)) <=? 4) &&
    List.forallb (bounded 256) log.(EestTypes.EvmLog.topics) &&
    List.forallb (bounded 8) log.(EestTypes.EvmLog.data).

  Definition logs_hash (logs : list EestTypes.EvmLog.t) : option (list Z) :=
    if negb (List.forallb log_valid logs) then None else
    Some (Keccak256.hash (EthereumRlp.encode_list (List.map (fun log =>
      EthereumRlp.encode_list [
        EthereumRlp.encode_bytes (EthereumRlp.fixed_big_endian 20 log.(EestTypes.EvmLog.address));
        EthereumRlp.encode_list (List.map (fun topic =>
          EthereumRlp.encode_bytes (EthereumRlp.fixed_big_endian 32 topic)) log.(EestTypes.EvmLog.topics));
        EthereumRlp.encode_bytes log.(EestTypes.EvmLog.data)]) logs))).
End EthereumCommitment.
