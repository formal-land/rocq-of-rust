From Stdlib Require Import List ZArith.

Import ListNotations.
Open Scope Z_scope.

(** Ethereum RLP encoding, adapted from the parent rlp/Encode.v and
    rlp/Raw.v scalar/header/list functions. Byte lists use Z directly, so this
    module is independent of the parent Go integer and byte representations. *)
Module EthereumRlp.
  Module Item.
    Inductive t : Set :=
    | Bytes (value : list Z)
    | List (values : list t).
  End Item.

  Definition fixed_big_endian (width : nat) (value : Z) : list Z :=
    List.map (fun index =>
      Z.land (Z.shiftr value (8 * Z.of_nat (width - S index))) 255)
      (List.seq 0 width).

  Definition big_endian (value : Z) : list Z :=
    if value <=? 0 then []
    else fixed_big_endian (S (Z.to_nat (Z.log2 value / 8))) value.

  Definition integer_size (value : Z) : Z :=
    if value =? 0 then 0 else 1 + Z.log2 value / 8.

  Definition header (small_tag large_tag size : Z) : list Z :=
    if size <? 56 then [small_tag + size]
    else (large_tag + integer_size size) :: big_endian size.

  Definition encode_bytes (value : list Z) : list Z :=
    match value with
    | [byte] => if byte <? 128 then value else [129; byte]
    | _ => header 128 183 (Z.of_nat (List.length value)) ++ value
    end.

  Definition encode_list (children : list (list Z)) : list Z :=
    let content := List.concat children in
    header 192 247 (Z.of_nat (List.length content)) ++ content.

  Definition encode_uint (value : Z) : list Z := encode_bytes (big_endian value).

  Fixpoint encode (item : Item.t) : list Z :=
    match item with
    | Item.Bytes value => encode_bytes value
    | Item.List values =>
      let fix encode_children (values : list Item.t) : list (list Z) :=
        match values with
        | [] => []
        | item :: rest => encode item :: encode_children rest
        end in
      encode_list (encode_children values)
    end.
End EthereumRlp.
