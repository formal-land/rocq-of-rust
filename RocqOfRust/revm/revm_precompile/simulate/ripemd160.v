From Stdlib Require Import List ZArith.

Import ListNotations.
Open Scope Z_scope.

(** Independent executable RIPEMD-160 for byte-valued inputs, following the
    algorithm designers' specification:
    https://homes.esat.kuleuven.be/~bosselae/ripemd/rmd160.txt
    The vectors below do not prove correspondence with REVM's crypto provider. *)
Module Ripemd160.
  Definition word (value : Z) : Z := Z.land value 4294967295.
  Definition complement (value : Z) : Z := Z.lxor value 4294967295.
  Definition rotate_left (value shift : Z) : Z :=
    word (Z.lor (Z.shiftl value shift) (Z.shiftr value (32 - shift))).

  Definition nonlinear (round x y z : Z) : Z :=
    if round <? 16 then Z.lxor (Z.lxor x y) z else
    if round <? 32 then Z.lor (Z.land x y) (Z.land (complement x) z) else
    if round <? 48 then Z.lxor (Z.lor x (complement y)) z else
    if round <? 64 then Z.lor (Z.land x z) (Z.land y (complement z)) else
    Z.lxor x (Z.lor y (complement z)).

  Definition left_constant (round : Z) : Z :=
    if round <? 16 then 0 else
    if round <? 32 then 1518500249 else
    if round <? 48 then 1859775393 else
    if round <? 64 then 2400959708 else 2840853838.

  Definition right_constant (round : Z) : Z :=
    if round <? 16 then 1352829926 else
    if round <? 32 then 1548603684 else
    if round <? 48 then 1836072691 else
    if round <? 64 then 2053994217 else 0.

  Definition left_order : list nat :=
    [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15;
     7; 4; 13; 1; 10; 6; 15; 3; 12; 0; 9; 5; 2; 14; 11; 8;
     3; 10; 14; 4; 9; 15; 8; 1; 2; 7; 0; 6; 13; 11; 5; 12;
     1; 9; 11; 10; 0; 8; 12; 4; 13; 3; 7; 15; 14; 5; 6; 2;
     4; 0; 5; 9; 7; 12; 2; 10; 14; 1; 3; 8; 11; 6; 15; 13]%nat.

  Definition right_order : list nat :=
    [5; 14; 7; 0; 9; 2; 11; 4; 13; 6; 15; 8; 1; 10; 3; 12;
     6; 11; 3; 7; 0; 13; 5; 10; 14; 15; 8; 12; 4; 9; 1; 2;
     15; 5; 1; 3; 7; 14; 6; 9; 11; 8; 12; 2; 10; 0; 4; 13;
     8; 6; 4; 1; 3; 11; 15; 0; 5; 12; 2; 13; 9; 7; 10; 14;
     12; 15; 10; 4; 1; 5; 8; 7; 6; 2; 13; 14; 0; 3; 9; 11]%nat.

  Definition left_shifts : list Z :=
    [11; 14; 15; 12; 5; 8; 7; 9; 11; 13; 14; 15; 6; 7; 9; 8;
     7; 6; 8; 13; 11; 9; 7; 15; 7; 12; 15; 9; 11; 7; 13; 12;
     11; 13; 6; 7; 14; 9; 13; 15; 14; 8; 13; 6; 5; 12; 7; 5;
     11; 12; 14; 15; 14; 15; 9; 8; 9; 14; 5; 6; 8; 6; 5; 12;
     9; 15; 5; 11; 6; 8; 13; 12; 5; 12; 13; 14; 11; 8; 5; 6].

  Definition right_shifts : list Z :=
    [8; 9; 9; 11; 13; 15; 15; 5; 7; 7; 8; 11; 14; 14; 12; 6;
     9; 13; 15; 7; 12; 8; 9; 11; 7; 7; 12; 7; 6; 15; 13; 11;
     9; 7; 15; 11; 8; 6; 6; 14; 12; 13; 5; 14; 13; 13; 7; 5;
     15; 5; 8; 11; 14; 14; 6; 14; 6; 9; 12; 9; 12; 5; 15; 8;
     8; 5; 12; 9; 12; 5; 14; 6; 8; 13; 6; 5; 15; 13; 11; 11].

  Definition initial : list Z :=
    [1732584193; 4023233417; 2562383102; 271733878; 3285377520].

  Fixpoint little_endian (count : nat) (value : Z) : list Z :=
    match count with
    | O => []
    | S rest => Z.land value 255 :: little_endian rest (Z.shiftr value 8)
    end.

  (** The fixed-width length field retains the low 64 bits of the bit length. *)
  Definition pad (input : list Z) : list Z :=
    let size := Z.of_nat (List.length input) in
    input ++ [128] ++ List.repeat 0 (Z.to_nat ((55 - size) mod 64)) ++
    little_endian 8 (size * 8).

  Fixpoint parse_words (input : list Z) : list Z :=
    match input with
    | a :: b :: c :: d :: rest =>
      (a + b * 256 + c * 65536 + d * 16777216) :: parse_words rest
    | _ => []
    end.

  Definition step (state : list Z) (round constant message shift : Z) : list Z :=
    match state with
    | [a; b; c; d; e] =>
      let next := word
        (rotate_left (word (a + nonlinear round b c d + message + constant)) shift + e) in
      [e; next; b; rotate_left c 10; d]
    | _ => state
    end.

  Fixpoint rounds (order : list nat) (shifts words state : list Z)
      (round : Z) (right : bool) : list Z :=
    match order, shifts with
    | index :: order_rest, shift :: shifts_rest =>
      let function_round := if right then 79 - round else round in
      let constant := if right then right_constant round else left_constant round in
      rounds order_rest shifts_rest words
        (step state function_round constant (List.nth index words 0) shift)
        (round + 1) right
    | _, _ => state
    end.

  Definition compress (state block : list Z) : list Z :=
    let words := parse_words block in
    let left := rounds left_order left_shifts words state 0 false in
    let right := rounds right_order right_shifts words state 0 true in
    match state, left, right with
    | [h0; h1; h2; h3; h4], [a; b; c; d; e], [a'; b'; c'; d'; e'] =>
      [word (h1 + c + d'); word (h2 + d + e'); word (h3 + e + a');
       word (h4 + a + b'); word (h0 + b + c')]
    | _, _, _ => state
    end.

  Fixpoint blocks (count : nat) (input state : list Z) : list Z :=
    match count with
    | O => state
    | S rest => blocks rest (List.skipn 64 input)
        (compress state (List.firstn 64 input))
    end.

  Definition hash (input : list Z) : list Z :=
    let padded := pad input in
    List.flat_map (little_endian 4)
      (blocks (List.length padded / 64)%nat padded initial).
End Ripemd160.

Module Test.
  (** Expected digests were computed independently using Python hashlib's
      RIPEMD-160 implementation. *)
  Lemma empty :
    Ripemd160.hash ([]) =
      [156; 17; 133; 165; 197; 233; 252; 84; 97; 40;
       8; 151; 126; 232; 245; 72; 178; 37; 141; 49].
  Proof. vm_compute. reflexivity. Qed.

  Lemma abc :
    Ripemd160.hash ([97; 98; 99]) =
      [142; 178; 8; 247; 224; 93; 152; 122; 155; 4;
       74; 142; 152; 198; 176; 135; 241; 90; 11; 252].
  Proof. vm_compute. reflexivity. Qed.

  Lemma padding_55 :
    Ripemd160.hash (List.repeat 97 55) =
      [13; 138; 140; 144; 99; 164; 133; 118; 167; 201;
       126; 159; 149; 37; 58; 110; 83; 255; 103; 101].
  Proof. vm_compute. reflexivity. Qed.

  Lemma padding_56 :
    Ripemd160.hash (List.repeat 97 56) =
      [231; 35; 52; 180; 108; 131; 204; 112; 190; 249;
       121; 225; 84; 83; 112; 108; 149; 184; 136; 190].
  Proof. vm_compute. reflexivity. Qed.

  Lemma padding_63 :
    Ripemd160.hash (List.repeat 97 63) =
      [230; 64; 4; 18; 147; 254; 102; 59; 155; 243;
       248; 194; 31; 254; 202; 192; 56; 25; 230; 178].
  Proof. vm_compute. reflexivity. Qed.

  Lemma padding_64 :
    Ripemd160.hash (List.repeat 97 64) =
      [157; 251; 125; 55; 74; 217; 36; 243; 248; 141;
       233; 98; 145; 195; 62; 154; 190; 213; 62; 50].
  Proof. vm_compute. reflexivity. Qed.

  Lemma padding_65 :
    Ripemd160.hash (List.repeat 97 65) =
      [153; 114; 75; 177; 24; 17; 231; 22; 106; 243;
       143; 103; 27; 106; 8; 45; 138; 180; 150; 11].
  Proof. vm_compute. reflexivity. Qed.

  Lemma multiple_blocks :
    Ripemd160.hash (List.map Z.of_nat (List.seq 0 128)) =
      [124; 77; 54; 7; 12; 30; 17; 118; 178; 150;
       10; 27; 13; 210; 49; 157; 84; 124; 248; 235].
  Proof. vm_compute. reflexivity. Qed.

End Test.
