Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.

Module Host.
  Class C
      (Self : Set) `{Link Self} :
      Type := {
    (* fn load_account_delegated(&mut self, address: Address) -> Option<AccountLoad>; *)
    load_account_delegated :
      forall
        (self : Self)
        (address : Address.t),
      option AccountLoad.t *
      Self;
  }.

  Module Eq.
    Class t
        {Self : Set} `{Link Self}
        {types : Host.Types.t} `{Host.Types.AreLinks types}
        `{!Host.Run Self types}
        (I : C Self) :
        Prop := {
      load_account_delegated
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (address : Address.t)
          (stack : Stack.t) :
        let ref_self : '&mut Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_load_account_delegated ref_self address)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(load_account_delegated) self address in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }}
    }.
    End Eq.
End Host.
