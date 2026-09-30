From Stdlib Require Import List ZArith.

Import ListNotations.
Open Scope Z_scope.

(** Executable SHA-256 for byte-valued inputs. This independent implementation
    follows the SHA-256 padding, schedule, and compression algorithm. Concrete
    vectors below do not establish correspondence with REVM's crypto provider. *)
Module Sha256.
  Definition word (x : Z) : Z := Z.land x 4294967295.

  Definition rotate (x shift : Z) : Z :=
    word (Z.lor (Z.shiftr x shift) (Z.shiftl x (32 - shift))).

  Definition xor3 (x y z : Z) : Z := Z.lxor (Z.lxor x y) z.
  Definition small_sigma0 (x : Z) : Z :=
    xor3 (rotate x 7) (rotate x 18) (Z.shiftr x 3).
  Definition small_sigma1 (x : Z) : Z :=
    xor3 (rotate x 17) (rotate x 19) (Z.shiftr x 10).
  Definition big_sigma0 (x : Z) : Z :=
    xor3 (rotate x 2) (rotate x 13) (rotate x 22).
  Definition big_sigma1 (x : Z) : Z :=
    xor3 (rotate x 6) (rotate x 11) (rotate x 25).

  Definition initial : list Z :=
    [1779033703; 3144134277; 1013904242; 2773480762;
     1359893119; 2600822924; 528734635; 1541459225].

  Definition constants : list Z :=
    [1116352408; 1899447441; 3049323471; 3921009573;
     961987163; 1508970993; 2453635748; 2870763221;
     3624381080; 310598401; 607225278; 1426881987;
     1925078388; 2162078206; 2614888103; 3248222580;
     3835390401; 4022224774; 264347078; 604807628;
     770255983; 1249150122; 1555081692; 1996064986;
     2554220882; 2821834349; 2952996808; 3210313671;
     3336571891; 3584528711; 113926993; 338241895;
     666307205; 773529912; 1294757372; 1396182291;
     1695183700; 1986661051; 2177026350; 2456956037;
     2730485921; 2820302411; 3259730800; 3345764771;
     3516065817; 3600352804; 4094571909; 275423344;
     430227734; 506948616; 659060556; 883997877;
     958139571; 1322822218; 1537002063; 1747873779;
     1955562222; 2024104815; 2227730452; 2361852424;
     2428436474; 2756734187; 3204031479; 3329325298].

  (** Encoding a fixed number of bytes also reduces the bit length modulo 2^64. *)
  Fixpoint big_endian (count : nat) (value : Z) : list Z :=
    match count with
    | O => []
    | S rest =>
      Z.land (Z.shiftr value (8 * Z.of_nat rest)) 255 :: big_endian rest value
    end.

  Definition pad (input : list Z) : list Z :=
    let size := Z.of_nat (List.length input) in
    input ++ [128] ++ List.repeat 0 (Z.to_nat ((55 - size) mod 64)) ++
    big_endian 8 (size * 8).

  Fixpoint parse_words (input : list Z) : list Z :=
    match input with
    | a :: b :: c :: d :: rest =>
      (a * 16777216 + b * 65536 + c * 256 + d) :: parse_words rest
    | _ => []
    end.

  (** The window contains W[t-16] through W[t-1], oldest first. *)
  Fixpoint extend_schedule (count : nat) (window : list Z) : list Z :=
    match count with
    | O => []
    | S rest =>
      let next := word
        (small_sigma1 (List.nth 14 window 0) + List.nth 9 window 0 +
         small_sigma0 (List.nth 1 window 0) + List.nth 0 window 0) in
      next :: extend_schedule rest (List.tl window ++ [next])
    end.

  Definition round (state : list Z) (constant message : Z) : list Z :=
    match state with
    | [a; b; c; d; e; f; g; h] =>
      let choose := Z.lxor (Z.land e f) (Z.land (Z.lxor e 4294967295) g) in
      let majority := xor3 (Z.land a b) (Z.land a c) (Z.land b c) in
      let t1 := word (h + big_sigma1 e + choose + constant + message) in
      let t2 := word (big_sigma0 a + majority) in
      [word (t1 + t2); a; b; c; word (d + t1); e; f; g]
    | _ => state
    end.

  Fixpoint rounds (round_constants schedule state : list Z) : list Z :=
    match round_constants, schedule with
    | constant :: constants_rest, message :: schedule_rest =>
      rounds constants_rest schedule_rest (round state constant message)
    | _, _ => state
    end.

  Definition compress (state block : list Z) : list Z :=
    let words := parse_words block in
    let schedule := words ++ extend_schedule 48 words in
    List.map (fun pair => word (fst pair + snd pair))
      (List.combine state (rounds constants schedule state)).

  Fixpoint blocks (count : nat) (input state : list Z) : list Z :=
    match count with
    | O => state
    | S rest => blocks rest (List.skipn 64 input)
        (compress state (List.firstn 64 input))
    end.

  Definition hash (input : list Z) : list Z :=
    let padded := pad input in
    List.flat_map (big_endian 4)
      (blocks (List.length padded / 64)%nat padded initial).
End Sha256.

Module Test.
  (** Expected digests were computed independently using Python hashlib.sha256. *)
  Lemma empty :
    Sha256.hash ([]) =
      [ 227; 176; 196; 66; 152; 252; 28; 20;
      154; 251; 244; 200; 153; 111; 185; 36;
      39; 174; 65; 228; 100; 155; 147; 76;
      164; 149; 153; 27; 120; 82; 184; 85 ].
  Proof. vm_compute. reflexivity. Qed.

  Lemma abc :
    Sha256.hash ([97; 98; 99]) =
      [ 186; 120; 22; 191; 143; 1; 207; 234;
      65; 65; 64; 222; 93; 174; 34; 35;
      176; 3; 97; 163; 150; 23; 122; 156;
      180; 16; 255; 97; 242; 0; 21; 173 ].
  Proof. vm_compute. reflexivity. Qed.

  Lemma padding_55 :
    Sha256.hash (List.repeat 97 55) =
      [ 159; 67; 144; 248; 211; 12; 45; 217;
      46; 201; 240; 149; 182; 94; 43; 154;
      233; 176; 169; 37; 165; 37; 142; 36;
      28; 159; 30; 145; 15; 115; 67; 24 ].
  Proof. vm_compute. reflexivity. Qed.

  Lemma padding_56 :
    Sha256.hash (List.repeat 97 56) =
      [ 179; 84; 57; 164; 172; 111; 9; 72;
      182; 214; 249; 227; 198; 175; 15; 95;
      89; 12; 226; 15; 27; 222; 112; 144;
      239; 121; 112; 104; 110; 198; 115; 138 ].
  Proof. vm_compute. reflexivity. Qed.

  Lemma padding_63 :
    Sha256.hash (List.repeat 97 63) =
      [ 125; 62; 116; 160; 93; 125; 177; 91;
      206; 74; 217; 236; 6; 88; 234; 152;
      227; 240; 110; 238; 207; 22; 180; 198;
      255; 242; 218; 69; 125; 220; 47; 52 ].
  Proof. vm_compute. reflexivity. Qed.

  Lemma padding_64 :
    Sha256.hash (List.repeat 97 64) =
      [ 255; 224; 84; 254; 122; 224; 203; 109;
      198; 92; 58; 249; 182; 29; 82; 9;
      244; 57; 133; 29; 180; 61; 11; 165;
      153; 115; 55; 223; 21; 70; 104; 235 ].
  Proof. vm_compute. reflexivity. Qed.

  Lemma padding_65 :
    Sha256.hash (List.repeat 97 65) =
      [ 99; 83; 97; 196; 139; 185; 234; 177;
      65; 152; 231; 110; 168; 171; 127; 26;
      65; 104; 93; 106; 214; 42; 169; 20;
      109; 48; 29; 79; 23; 235; 10; 224 ].
  Proof. vm_compute. reflexivity. Qed.

  Lemma multiple_blocks :
    Sha256.hash (List.map Z.of_nat (List.seq 0 128)) =
      [ 71; 31; 185; 67; 170; 35; 197; 17;
      246; 247; 47; 141; 22; 82; 217; 200;
      128; 207; 163; 146; 173; 128; 80; 49;
      32; 84; 119; 3; 229; 106; 43; 229 ].
  Proof. vm_compute. reflexivity. Qed.

End Test.
