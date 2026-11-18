From Stdlib Require Import Bool List ZArith.
Import ListNotations.
Open Scope Z_scope.

Module Blake2.
  Definition mask : Z := 2 ^ 64 - 1.

  Definition word (x : Z) : Z := Z.land x mask.

  Definition rotate (x n : Z) : Z :=
    word (Z.lor (Z.shiftr x n) (Z.shiftl x (64 - n))).

  Definition iv : list Z :=
    [0x6a09e667f3bcc908; 0xbb67ae8584caa73b; 0x3c6ef372fe94f82b;
     0xa54ff53a5f1d36f1; 0x510e527fade682d1; 0x9b05688c2b3e6c1f;
     0x1f83d9abfb41bd6b; 0x5be0cd19137e2179].

  Definition sigma : list (list nat) :=
    [[0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15];
     [14;10;4;8;9;15;13;6;1;12;0;2;11;7;5;3];
     [11;8;12;0;5;2;15;13;10;14;3;6;7;1;9;4];
     [7;9;3;1;13;12;11;14;2;6;5;10;4;0;15;8];
     [9;0;5;7;2;4;10;15;14;1;11;12;6;8;3;13];
     [2;12;6;10;0;11;8;3;4;13;7;5;15;14;1;9];
     [12;5;1;15;14;13;4;10;0;7;6;3;9;2;8;11];
     [13;11;7;14;12;1;3;9;5;0;15;4;8;6;2;10];
     [6;15;14;9;11;3;0;8;12;2;13;7;1;4;10;5];
     [10;2;8;4;7;6;1;5;15;11;9;14;3;12;13;0]]%nat.

  Fixpoint put (index : nat) (value : Z) (values : list Z) : list Z :=
    match index, values with
    | O, _ :: rest => value :: rest
    | S i, head :: rest => head :: put i value rest
    | _, [] => []
    end.

  Definition g (v : list Z) (a b c d : nat) (x y : Z) : list Z :=
    let va := word (List.nth a v 0 + List.nth b v 0 + x) in
    let vd := rotate (Z.lxor (List.nth d v 0) va) 32 in
    let vc := word (List.nth c v 0 + vd) in
    let vb := rotate (Z.lxor (List.nth b v 0) vc) 24 in
    let va := word (va + vb + y) in
    let vd := rotate (Z.lxor vd va) 16 in
    let vc := word (vc + vd) in
    let vb := rotate (Z.lxor vb vc) 63 in
    put d vd (put c vc (put b vb (put a va v))).

  Definition round (m : list Z) (r : Z) (v : list Z) : list Z :=
    let s := List.nth (Z.to_nat (r mod 10)) sigma [] in
    let msg := fun i => List.nth (List.nth i s 0%nat) m 0 in
    let v := g v 0%nat 4%nat 8%nat 12%nat (msg 0%nat) (msg 1%nat) in
    let v := g v 1%nat 5%nat 9%nat 13%nat (msg 2%nat) (msg 3%nat) in
    let v := g v 2%nat 6%nat 10%nat 14%nat (msg 4%nat) (msg 5%nat) in
    let v := g v 3%nat 7%nat 11%nat 15%nat (msg 6%nat) (msg 7%nat) in
    let v := g v 0%nat 5%nat 10%nat 15%nat (msg 8%nat) (msg 9%nat) in
    let v := g v 1%nat 6%nat 11%nat 12%nat (msg 10%nat) (msg 11%nat) in
    let v := g v 2%nat 7%nat 8%nat 13%nat (msg 12%nat) (msg 13%nat) in
    g v 3%nat 4%nat 9%nat 14%nat (msg 14%nat) (msg 15%nat).
  (** Binary recursion avoids allocating a unary counter for the u32 rounds.
      The exact requested work is performed; external runner time/memory limits
      remain resource failures, never an alternative successful digest. *)
  Fixpoint rounds_positive (count : positive) (m : list Z)
      (state : Z * list Z) : Z * list Z :=
    let step := fun state => let '(r, v) := state in
      ((r + 1) mod 10, round m r v) in
    match count with
    | xH => step state
    | xO p => rounds_positive p m (rounds_positive p m state)
    | xI p => step (rounds_positive p m (rounds_positive p m state))
    end.

  Definition compress (count : Z) (h m : list Z) (t0 t1 : Z)
      (final_block : bool) : list Z :=
    let v := h ++ iv in
    let v := put 12 (Z.lxor (List.nth 12 v 0) t0) v in
    let v := put 13 (Z.lxor (List.nth 13 v 0) t1) v in
    let v := if final_block then put 14 (Z.lxor (List.nth 14 v 0) mask) v else v in
    let v := match count with Zpos p => snd (rounds_positive p m (0, v)) | _ => v end in
    List.map (fun i => Z.lxor (List.nth i h 0)
      (Z.lxor (List.nth i v 0) (List.nth (i + 8)%nat v 0))) (List.seq 0 8).

  Definition decode_be (bytes : list Z) : Z :=
    List.fold_left (fun value byte => 256 * value + byte) bytes 0.

  Definition decode_le (bytes : list Z) : Z := decode_be (List.rev bytes).

  Definition read_words (input : list Z) (offset count : nat) : list Z :=
    List.map (fun i => decode_le (List.firstn 8 (List.skipn (offset + 8 * i) input)))
      (List.seq 0 count).

  Definition encode_word (value : Z) : list Z :=
    List.map (fun i => Z.land (Z.shiftr value (8 * Z.of_nat i)) 255) (List.seq 0 8).

  Module Result.
    Inductive t : Set :=
    | Success (cost : Z) (output : list Z)
    | WrongLength | OutOfGas | WrongFinalIndicatorFlag.
  End Result.

  Definition run (input : list Z) (gas_limit : Z) : Result.t :=
    if negb (Nat.eqb (List.length input) 213) then Result.WrongLength else
    let count := decode_be (List.firstn 4 input) in
    if gas_limit <? count then Result.OutOfGas else
    let flag := List.nth 212 input 0 in
    if negb ((flag =? 0) || (flag =? 1)) then Result.WrongFinalIndicatorFlag else
    let h := read_words input 4 8 in
    let m := read_words input 68 16 in
    let t0 := decode_le (List.firstn 8 (List.skipn 196 input)) in
    let t1 := decode_le (List.firstn 8 (List.skipn 204 input)) in
    Result.Success count (List.flat_map encode_word (compress count h m t0 t1 (flag =? 1))).
End Blake2.
