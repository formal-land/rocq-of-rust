(* ExtrOcamlZBigInt uses Big_int_Z.big_int, an alias for Z.t. *)
let of_big value = value
let json_z value =
    if Z.equal value Z.zero then `Int 0 else `Intlit (Z.to_string value)
