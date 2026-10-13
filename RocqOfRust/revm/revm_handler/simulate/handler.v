From Stdlib Require Import List ZArith.

Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_precompile.simulate.modexp.

Import ListNotations.
Open Scope Z_scope.

Module handler.
  (** handler.rs::first_frame_input resolves one delegation and warms its
      destination before entering the call checkpoint, without charging call
      opcode gas. The call context still uses the original target address. *)
  Definition first_frame_input (target : Z) (state : StatefulHost.t)
      : list Z * StatefulHost.t :=
    let state := StatefulHost.warm_account state target in
    let code := match StatefulHost.find_account target state.(StatefulHost.accounts) with
      | Some account => account.(StatefulHost.Account.code)
      | None => []
      end in
    match code with
    | 239 :: 1 :: 0 :: address =>
      if Nat.eqb (List.length address) 20 then
        let delegate := Modexp.decode_be address in
        let state := StatefulHost.warm_account state delegate in
        let code := match StatefulHost.find_account delegate state.(StatefulHost.accounts) with
          | Some account => account.(StatefulHost.Account.code)
          | None => []
          end in
        (code, state)
      else (code, state)
    | _ => (code, state)
    end.
End handler.
