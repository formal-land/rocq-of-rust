From Stdlib Require Import Bool List ZArith.

Require Import revm.revm_handler.simulate.ethereum_rlp.
Require Import revm.revm_precompile.simulate.modexp.

Import ListNotations.
Open Scope Z_scope.

Module EthereumRlpDecode.
  Definition byte_valid (byte : Z) : bool := (0 <=? byte) && (byte <? 256).

  Definition split_payload (size : Z) (input : list Z) : option (list Z * list Z) :=
    if (size <? 0) || (Z.of_nat (List.length input) <? size) then None else
    Some (List.firstn (Z.to_nat size) input, List.skipn (Z.to_nat size) input).

  Definition long_payload (length_size : Z) (input : list Z) :
      option (list Z * list Z) :=
    match split_payload length_size input with
    | Some (length_bytes, rest) =>
        if List.hd 0 length_bytes =? 0 then None else
        let size := Modexp.decode_be length_bytes in
        if size <? 56 then None else split_payload size rest
    | None => None
    end.

  Definition header (prefix : Z) (rest : list Z) :
      option (bool * list Z * list Z) :=
    let is_list := 192 <=? prefix in
    let payload :=
      if prefix <? 184 then split_payload (prefix - 128) rest else
      if prefix <? 192 then long_payload (prefix - 183) rest else
      if prefix <? 248 then split_payload (prefix - 192) rest else
      long_payload (prefix - 247) rest in
    match payload with
    | Some (body, tail) =>
        if negb is_list && (Z.of_nat (List.length body) =? 1) &&
          (List.hd 0 body <? 128) then None else
        Some (is_list, body, tail)
    | None => None
    end.

  Fixpoint parse (fuel : nat) (input : list Z) {struct fuel} :
      option (EthereumRlp.Item.t * list Z) :=
    match fuel with
    | O => None
    | S rest_fuel =>
        match input with
        | [] => None
        | prefix :: rest =>
            if prefix <? 128 then Some (EthereumRlp.Item.Bytes [prefix], rest) else
            match header prefix rest with
            | Some (false, body, tail) => Some (EthereumRlp.Item.Bytes body, tail)
            | Some (true, body, tail) =>
                match parse_list rest_fuel body with
                | Some children => Some (EthereumRlp.Item.List children, tail)
                | None => None
                end
            | None => None
            end
        end
    end
  with parse_list (fuel : nat) (input : list Z) {struct fuel} :
      option (list EthereumRlp.Item.t) :=
    match input with
    | [] => Some []
    | _ =>
        match fuel with
        | O => None
        | S rest_fuel =>
            match parse rest_fuel input with
            | Some (item, tail) =>
                match parse_list rest_fuel tail with
                | Some children => Some (item :: children)
                | None => None
                end
            | None => None
            end
        end
    end.

  Definition decode (input : list Z) : option EthereumRlp.Item.t :=
    if negb (List.forallb byte_valid input) then None else
    match parse (S ((2 * List.length input)%nat)) input with
    | Some (item, []) => Some item
    | _ => None
    end.
End EthereumRlpDecode.
