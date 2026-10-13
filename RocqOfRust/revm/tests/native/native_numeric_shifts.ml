(* Numeric extraction boundary only. Preserve Rocq's arbitrary signed shift
   counts rather than the Stdlib mapping's eager machine-int conversion.
   Nonrepresentable left shifts of nonzero values remain resource failures.
   This exception never produces an EVM result or a successful comparison. *)
exception Numeric_resource_limit

let shiftr_nonnegative value count =
    if Z.geq count (Z.of_int (Z.numbits value)) then
        if Z.sign value < 0 then Z.minus_one else Z.zero
    else Z.shift_right value (Z.to_int count)

let shiftl_nonnegative value count =
    if Z.equal value Z.zero then Z.zero
    else if Z.fits_int count then Z.shift_left value (Z.to_int count)
    else raise Numeric_resource_limit

let shiftl value count =
    if Z.sign count < 0 then shiftr_nonnegative value (Z.neg count)
    else shiftl_nonnegative value count

let shiftr value count =
    if Z.sign count < 0 then shiftl_nonnegative value (Z.neg count)
    else shiftr_nonnegative value count
