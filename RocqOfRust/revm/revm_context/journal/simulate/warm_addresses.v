Require Import simulate.RocqOfRust.
From Stdlib Require Import List.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.links.aliases.
Require Import ruint.links.lib.

Import ListNotations.

Module WarmAddresses.
  Record t : Set := {
    precompile_set : list Address.t;
    precompile_short_addresses : list bool;
    precompile_all_short_addresses : bool;
    coinbase : option Address.t;
    access_list : list (Address.t * list aliases.U256.t);
  }.
End WarmAddresses.

Module Impl_WarmAddresses.
  (** primitives::short_address, using the existing integer Address model. *)
  Definition short_address (address : Address.t) : option usize :=
    if Z.ltb address.(Address.value) 300 then Some {| Integer.value := address.(Address.value) |}
    else None.

  Definition new : WarmAddresses.t := {|
    WarmAddresses.precompile_set := [];
    WarmAddresses.precompile_short_addresses := List.repeat false 300;
    WarmAddresses.precompile_all_short_addresses := true;
    WarmAddresses.coinbase := None;
    WarmAddresses.access_list := [];
  |}.

  Definition set_precompile_addresses (self : WarmAddresses.t) (addresses : list Address.t)
      : WarmAddresses.t :=
    let '(bits, all_short_addresses) := List.fold_left
      (fun '(bits, all_short_addresses) address =>
        match short_address address with
        | Some index =>
          let index := Z.to_nat index.(Integer.value) in
          (List.firstn index bits ++ true :: List.skipn (S index) bits, all_short_addresses)
        | None => (bits, false)
        end) addresses (List.repeat false 300, true) in
    self <| WarmAddresses.precompile_short_addresses := bits |>
      <| WarmAddresses.precompile_all_short_addresses := all_short_addresses |>
      <| WarmAddresses.precompile_set := addresses |>.

  Definition set_coinbase (self : WarmAddresses.t) (address : Address.t) : WarmAddresses.t :=
    self <| WarmAddresses.coinbase := Some address |>.

  Definition set_access_list (self : WarmAddresses.t)
      (access_list : list (Address.t * list aliases.U256.t)) : WarmAddresses.t :=
    self <| WarmAddresses.access_list := access_list |>.

  Definition clear_coinbase (self : WarmAddresses.t) : WarmAddresses.t :=
    self <| WarmAddresses.coinbase := None |>.

  Definition clear_coinbase_and_access_list (self : WarmAddresses.t) : WarmAddresses.t :=
    self <| WarmAddresses.coinbase := None |> <| WarmAddresses.access_list := [] |>.

  Definition is_warm (self : WarmAddresses.t) (address : Address.t) : bool :=
    if match self.(WarmAddresses.coinbase) with
      | Some coinbase => Z.eqb address.(Address.value) coinbase.(Address.value)
      | None => false
      end then true else
    if List.existsb (fun entry => Z.eqb address.(Address.value) (fst entry).(Address.value))
      self.(WarmAddresses.access_list) then true else
    match self.(WarmAddresses.precompile_set) with
    | [] => false
    | _ => match short_address address with
      | Some index => List.nth (Z.to_nat index.(Integer.value))
          self.(WarmAddresses.precompile_short_addresses) false
      | None => if negb self.(WarmAddresses.precompile_all_short_addresses) then
          List.existsb (fun key => Z.eqb address.(Address.value) key.(Address.value))
            self.(WarmAddresses.precompile_set)
          else false
      end
    end.

  Definition is_storage_warm (self : WarmAddresses.t) (address : Address.t)
      (key : aliases.U256.t) : bool :=
    match List.find (fun entry => Z.eqb address.(Address.value) (fst entry).(Address.value))
      self.(WarmAddresses.access_list) with
    | Some (_, keys) => List.existsb (fun slot => Z.eqb key.(Uint.value) slot.(Uint.value)) keys
    | None => false
    end.

  Definition is_cold (self : WarmAddresses.t) (address : Address.t) : bool :=
    negb (is_warm self address).
End Impl_WarmAddresses.
