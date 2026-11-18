module Big = Z
module N = Native_transactions

let rec positive_of_big value =
    if Big.equal value Big.one then N.XH
    else if Big.testbit value 0 then N.XI (positive_of_big (Big.shift_right value 1))
    else N.XO (positive_of_big (Big.shift_right value 1))

(* The bridge validates nonnegative JSON integers before this conversion. *)
let of_big value =
    if Big.equal value Big.zero then N.Z0 else N.Zpos (positive_of_big value)

let rec big_of_positive = function
| N.XH -> Big.one
| N.XO value -> Big.shift_left (big_of_positive value) 1
| N.XI value -> Big.succ (Big.shift_left (big_of_positive value) 1)

let json_z = function
| N.Z0 -> `Int 0
| N.Zpos value -> `Intlit (Big.to_string (big_of_positive value))
| N.Zneg value -> `Intlit (Big.to_string (Big.neg (big_of_positive value)))
