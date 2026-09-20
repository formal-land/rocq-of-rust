From Stdlib Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

Module Keccak256.
  (* Ethereum Keccak-256: rate 136 bytes, domain suffix 0x01, not SHA3's 0x06.
     Lanes use x + 5*y and little-endian bytes. *)
  Definition mask : Z := 18446744073709551615.
  Definition rot (a n : Z) : Z :=
    Z.land (Z.lor (Z.shiftl a n) (Z.shiftr a (64 - n))) mask.

  Definition rotations : list Z :=
    [0; 1; 62; 28; 27; 36; 44; 6; 55; 20; 3; 10; 43; 25; 39;
     41; 45; 15; 21; 8; 18; 2; 61; 56; 14].

  Definition round_constants : list Z :=
    [1; 32898; 9223372036854808714; 9223372039002292224;
     32907; 2147483649; 9223372039002292353; 9223372036854808585;
     138; 136; 2147516425; 2147483658; 2147516555;
     9223372036854775947; 9223372036854808713; 9223372036854808579;
     9223372036854808578; 9223372036854775936; 32778;
     9223372039002259466; 9223372039002292353; 9223372036854808704;
     2147483649; 9223372039002292232].

  Definition lane (a : list Z) (x y : nat) : Z :=
    nth (x + 5 * y)%nat a 0.

  Definition round (a : list Z) (rc : Z) : list Z :=
    let c := map (fun x =>
      fold_left Z.lxor (map (lane a x) (seq 0 5)) 0) (seq 0 5) in
    let d := map (fun x => Z.lxor (nth ((x + 4) mod 5)%nat c 0)
      (rot (nth ((x + 1) mod 5)%nat c 0) 1)) (seq 0 5) in
    let theta := map (fun i => Z.lxor (nth i a 0)
      (nth (i mod 5)%nat d 0)) (seq 0 25) in
    (* Inverse of (x,y) -> (y, 2*x+3*y): (x+3*y, x), modulo 5. *)
    let b := map (fun i =>
      let x := (i mod 5)%nat in
      let y := (i / 5)%nat in
      let source := (((x + 3*y) mod 5) + 5*x)%nat in
      rot (nth source theta 0) (nth source rotations 0)) (seq 0 25) in
    map (fun i =>
      let x := (i mod 5)%nat in
      let y := (i / 5)%nat in
      let chi := Z.lxor (nth i b 0)
        (Z.land (Z.lxor (lane b ((x+1) mod 5)%nat y) mask)
          (lane b ((x+2) mod 5)%nat y)) in
      if Nat.eqb i 0 then Z.lxor chi rc else chi) (seq 0 25).

  Definition permutation (a : list Z) : list Z :=
    fold_left round round_constants a.

  Fixpoint little_endian (bytes : list Z) : Z :=
    match bytes with
    | [] => 0
    | b :: rest => Z.lor (Z.land b 255) (Z.shiftl (little_endian rest) 8)
    end.

  Definition absorb_block (a bytes : list Z) : list Z :=
    permutation (map (fun i =>
      if Nat.ltb i 17 then
        Z.lxor (nth i a 0)
          (little_endian (firstn 8 (skipn (8*i)%nat bytes)))
      else nth i a 0) (seq 0 25)).

  Fixpoint absorb (blocks : nat) (a bytes : list Z) : list Z :=
    match blocks with
    | O => a
    | S rest => absorb rest (absorb_block a (firstn 136 bytes))
        (skipn 136 bytes)
    end.

  Definition hash (bytes : list Z) : list Z :=
    let remainder := (length bytes mod 136)%nat in
    let padded := bytes ++
      (if Nat.eqb remainder 135 then [129]
       else [1] ++ repeat 0 (134 - remainder)%nat ++ [128]) in
    let a := absorb (S (length bytes / 136)%nat) (repeat 0 25) padded in
    map (fun i => Z.land
      (Z.shiftr (nth (i / 8)%nat a 0) (8 * Z.of_nat (i mod 8))) 255)
      (seq 0 32).

  Module Test.
  (* Expected bytes independently obtained from PyCryptodome's Keccak-256. *)
  Example empty : hash [] =
    [197;210;70;1;134;247;35;60;146;126;125;178;220;199;3;192;
     229;0;182;83;202;130;39;59;123;250;216;4;93;133;164;112].
  Proof. vm_compute. reflexivity. Qed.

  Example abc : hash [97;98;99] =
    [78;3;101;122;234;69;169;79;199;212;123;168;38;200;214;103;
     192;209;230;227;58;100;160;54;236;68;245;143;161;45;108;69].
  Proof. vm_compute. reflexivity. Qed.

  Definition sequence (n : nat) := map (fun i => Z.of_nat (i mod 256)) (seq 0 n).
  Example rate_minus_one : hash (sequence 135) =
    [203;223;217;222;229;250;173;56;24;214;176;111;149;162;25;253;
     41;11;14;23;6;246;168;46;90;89;91;156;233;250;202;98].
  Proof. vm_compute. reflexivity. Qed.
  Example rate_exact : hash (sequence 136) =
    [124;231;89;241;171;127;156;228;55;113;153;112;194;107;10;102;
     255;17;254;62;56;225;125;248;156;245;210;156;125;127;128;126].
  Proof. vm_compute. reflexivity. Qed.
  Example rate_plus_one : hash (sequence 137) =
    [172;115;212;250;230;139;132;83;247;100;0;124;26;32;206;149;
     153;65;135;134;31;12;50;39;163;168;233;154;115;163;177;219].
  Proof. vm_compute. reflexivity. Qed.
  Example two_rates : hash (sequence 272) =
    [253;242;236;73;231;73;150;13;60;133;33;160;33;154;248;208;
     62;48;226;179;191;25;189;22;21;14;224;234;241;51;214;110].
  Proof. vm_compute. reflexivity. Qed.
  End Test.
End Keccak256.
