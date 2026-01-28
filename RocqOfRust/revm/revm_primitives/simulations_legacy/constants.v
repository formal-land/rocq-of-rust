Require Import links.RocqOfRust.

(* pub const BLOCK_HASH_HISTORY: u64 = 256; *)
Definition BLOCK_HASH_HISTORY : u64 := {|
  Integer.value := 256;
|}.

(* pub const BLOCKHASH_SERVE_WINDOW: usize = 8192; *)
Definition BLOCKHASH_SERVE_WINDOW : usize := {|
  Integer.value := 8192;
|}.
