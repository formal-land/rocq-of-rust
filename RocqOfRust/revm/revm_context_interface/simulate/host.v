Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.log.links.mod.
Require Import core.links.result.
Require Import revm.revm_context_interface.links.block.
Require Import revm.revm_context_interface.links.cfg.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.block.
Require Import revm.revm_context_interface.simulate.cfg.
Require Import revm.revm_context_interface.simulate.transaction.

Module Host.
  Class C
      (Self : Set) `{Link Self}
      (types : Host.Types.t) `{Host.Types.AreLinks types} :
      Type := {
    TransactionGetter_for_Self ::
      TransactionGetter.C
        Self
        types.(Host.Types.Transaction)
        types.(Host.Types.TransactionTypes);
    BlockGetter_for_Self ::
      BlockGetter.C
        Self
        (Host.Types.to_BlockGetter_types types);
    CfgGetter_for_Self ::
      CfgGetter.C
        Self
        (Host.Types.to_CfgGetter_types types);
    (* fn load_account_delegated(&mut self, address: Address) -> Option<AccountLoad>; *)
    load_account_delegated
      (self : Self)
      (address : Address.t) :
      option AccountLoad.t * Self;
    (* fn block_hash(&mut self, number: u64) -> Option<B256>; *)
    block_hash
      (self : Self)
      (number : u64) :
      option aliases.B256.t * Self;
    (* fn balance(&mut self, address: Address) -> Option<StateLoad<U256>>; *)
    balance
      (self : Self)
      (address : Address.t) :
      option (StateLoad.t aliases.U256.t) * Self;
    (* fn code(&mut self, address: Address) -> Option<Eip7702CodeLoad<Bytes>>; *)
    code
      (self : Self)
      (address : Address.t) :
      option (Eip7702CodeLoad.t Bytes.t) * Self;
    (* fn code_hash(&mut self, address: Address) -> Option<Eip7702CodeLoad<B256>>; *)
    code_hash
      (self : Self)
      (address : Address.t) :
      option (Eip7702CodeLoad.t aliases.B256.t) * Self;
    (* fn sload(&mut self, address: Address, index: U256) -> Option<StateLoad<U256>>; *)
    sload
      (self : Self)
      (address : Address.t)
      (index : aliases.U256.t) :
      option (StateLoad.t aliases.U256.t) * Self;
    (*
    fn sstore(
        &mut self,
        address: Address,
        index: U256,
        value: U256,
    ) -> Option<StateLoad<SStoreResult>>;
    *)
    sstore
      (self : Self)
      (address : Address.t)
      (index : aliases.U256.t)
      (value : aliases.U256.t) :
      option (StateLoad.t SStoreResult.t) * Self;
    (* fn tload(&mut self, address: Address, index: U256) -> U256; *)
    tload
      (self : Self)
      (address : Address.t)
      (index : aliases.U256.t) :
      aliases.U256.t * Self;
    (* fn tstore(&mut self, address: Address, index: U256, value: U256); *)
    tstore
      (self : Self)
      (address : Address.t)
      (index : aliases.U256.t)
      (value : aliases.U256.t) :
      Self;
    (* fn log(&mut self, log: Log); *)
    log
      (self : Self)
      (log' : Log.t LogData.t) :
      Self;
    (*
    fn selfdestruct(
        &mut self,
        address: Address,
        target: Address,
        skip_cold_load: bool,
    ) -> Result<StateLoad<SelfDestructResult>, LoadError>;
    *)
    selfdestruct
      (self : Self)
      (address : Address.t)
      (target : Address.t)
      (skip_cold_load : bool) :
      Result.t (StateLoad.t SelfDestructResult.t) LoadError.t * Self;
  }.

  Module Eq.
    Class t
        {Self : Set} `{Link Self}
        {types : Host.Types.t} `{Host.Types.AreLinks types}
        `{!Host.Run Self types}
        (I : C Self types) :
        Prop := {
      TransactionGetter_for_Self ::
        TransactionGetter.Eq.t I.(TransactionGetter_for_Self);
      BlockGetter_for_Self :: BlockGetter.Eq.t I.(BlockGetter_for_Self);
      CfgGetter_for_Self :: CfgGetter.Eq.t I.(CfgGetter_for_Self);
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
        }};
      block_hash
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (number : u64)
          (stack : Stack.t) :
        let ref_self : '&mut Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_block_hash ref_self number)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(block_hash) self number in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }};
      balance
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (address : Address.t)
          (stack : Stack.t) :
        let ref_self : '&mut Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_balance ref_self address)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(balance) self address in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }};
      code
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (address : Address.t)
          (stack : Stack.t) :
        let ref_self : '&mut Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_code ref_self address)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(code) self address in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }};
      code_hash
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (address : Address.t)
          (stack : Stack.t) :
        let ref_self : '&mut Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_code_hash ref_self address)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(code_hash) self address in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }};
      sload
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (address : Address.t)
          (index : aliases.U256.t)
          (stack : Stack.t) :
        let ref_self : '&mut Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_sload ref_self address index)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(sload) self address index in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }};
      sstore
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (address : Address.t)
          (index : aliases.U256.t)
          (value : aliases.U256.t)
          (stack : Stack.t) :
        let ref_self : '&mut Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_sstore ref_self address index value)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(sstore) self address index value in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }};
      tload
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (address : Address.t)
          (index : aliases.U256.t)
          (stack : Stack.t) :
        let ref_self : '&mut Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_tload ref_self address index)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(tload) self address index in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }};
      tstore
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (address : Address.t)
          (index : aliases.U256.t)
          (value : aliases.U256.t)
          (stack : Stack.t) :
        let ref_self : '&mut Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_tstore ref_self address index value)
            (interpreter :: self :: stack)%stack 🌲
          (
            Output.Success tt,
            (interpreter :: I.(tstore) self address index value :: stack)%stack
          )
        }};
      log
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (log' : Log.t LogData.t)
          (stack : Stack.t) :
        let ref_self : '&mut Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_log ref_self log')
            (interpreter :: self :: stack)%stack 🌲
          (
            Output.Success tt,
            (interpreter :: I.(log) self log' :: stack)%stack
          )
        }};
      selfdestruct
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (address : Address.t)
          (target : Address.t)
          (skip_cold_load : bool)
          (stack : Stack.t) :
        let ref_self : '&mut Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_selfdestruct ref_self address target skip_cold_load)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(selfdestruct) self address target skip_cold_load in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }}
    }.
  End Eq.
  Export (hints) Eq.
End Host.
Export (hints) Host.
