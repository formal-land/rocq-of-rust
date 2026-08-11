Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.fixed_FixedBytes.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import bytes.simulate.bytes.
Require Import alloy_primitives.log.links.mod.
Require Import core.links.result.
Require Import core.links.option.
Require Import revm.revm_context_interface.links.block.
Require Import revm.revm_context_interface.links.cfg.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_context_interface.simulate.block.
Require Import revm.revm_context_interface.simulate.cfg.
Require Import revm.revm_context_interface.simulate.journaled_state.
Require Import revm.revm_context_interface.simulate.transaction.
Require Import ruint.links.lib.
Require Import ruint.simulate.lib.

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
    (*
    fn load_account_info_skip_cold_load(
      &mut self,
      address: Address,
      load_code: bool,
      skip_cold_load: bool,
    ) -> Result<AccountInfoLoad, LoadError>;
    *)
    load_account_info_skip_cold_load
      (self : Self)
      (address : Address.t)
      (load_code : bool)
      (skip_cold_load : bool) :
      Result.t AccountInfoLoad.t LoadError.t * Self;
    (* fn load_account_delegated(&mut self, address: Address) -> Option<StateLoad<AccountLoad>>; *)
    load_account_delegated
      (self : Self)
      (address : Address.t) :
      option (StateLoad.t AccountLoad.t) * Self;
    (* fn load_account_code(&mut self, address: Address) -> Option<StateLoad<Bytes>>; *)
    load_account_code
      (self : Self)
      (address : Address.t) :
      option (StateLoad.t Bytes.t) * Self;
    (* fn block_hash(&mut self, number: u64) -> Option<B256>; *)
    block_hash
      (self : Self)
      (number : u64) :
      option aliases.B256.t * Self;
    (* fn max_initcode_size(&self) -> usize; *)
    max_initcode_size
      (self : Self) :
      usize * Self;
    (* fn beneficiary(&self) -> Address; *)
    beneficiary
      (self : Self) :
      Address.t * Self;
    (* fn block_number(&self) -> U256; *)
    block_number
      (self : Self) :
      aliases.U256.t * Self;
    (* fn timestamp(&self) -> U256; *)
    timestamp
      (self : Self) :
      aliases.U256.t * Self;
    (* fn gas_limit(&self) -> U256; *)
    gas_limit
      (self : Self) :
      aliases.U256.t * Self;
    (* fn chain_id(&self) -> U256; *)
    chain_id
      (self : Self) :
      aliases.U256.t * Self;
    (* fn basefee(&self) -> U256; *)
    basefee
      (self : Self) :
      aliases.U256.t * Self;
    (* fn blob_gasprice(&self) -> U256; *)
    blob_gasprice
      (self : Self) :
      aliases.U256.t * Self;
    (* fn effective_gas_price(&self) -> U256; *)
    effective_gas_price
      (self : Self) :
      aliases.U256.t * Self;
    (* fn caller(&self) -> Address; *)
    caller
      (self : Self) :
      Address.t * Self;
    (* fn blob_hash(&self, number: usize) -> Option<U256>; *)
    blob_hash
      (self : Self)
      (number : usize) :
      option aliases.U256.t * Self;
    (* fn difficulty(&self) -> U256; *)
    difficulty
      (self : Self) :
      aliases.U256.t * Self;
    (* fn prevrandao(&self) -> Option<U256>; *)
    prevrandao
      (self : Self) :
      option aliases.U256.t * Self;
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
    fn sload_skip_cold_load(
      &mut self,
      address: Address,
      key: U256,
      skip_cold_load: bool,
    ) -> Result<StateLoad<U256>, LoadError>;
    *)
    sload_skip_cold_load
      (self : Self)
      (address : Address.t)
      (key : aliases.U256.t)
      (skip_cold_load : bool) :
      Result.t (StateLoad.t aliases.U256.t) LoadError.t * Self;
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
    (*
    fn sstore_skip_cold_load(
      &mut self,
      address: Address,
      key: U256,
      value: U256,
      skip_cold_load: bool,
    ) -> Result<StateLoad<SStoreResult>, LoadError>;
    *)
    sstore_skip_cold_load
      (self : Self)
      (address : Address.t)
      (key : aliases.U256.t)
      (value : aliases.U256.t)
      (skip_cold_load : bool) :
      Result.t (StateLoad.t SStoreResult.t) LoadError.t * Self;
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
      load_account_info_skip_cold_load
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (address : Address.t)
          (load_code : bool)
          (skip_cold_load : bool)
          (stack : Stack.t) :
        let ref_self : '&mut Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_load_account_info_skip_cold_load ref_self address load_code skip_cold_load)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(load_account_info_skip_cold_load) self address load_code skip_cold_load in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }};
      (** A successful code-loading call must return an account whose generated
          code observation is present and agrees with the pure host model. *)
      load_account_info_skip_cold_load_code_len
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self self_after : Self)
          (address : Address.t)
          (skip_cold_load : bool)
          (account : AccountInfoLoad.t)
          (stack : Stack.t)
          (ref_account : '& AccountInfoLoad.t) :
        I.(Host.load_account_info_skip_cold_load)
            self address true skip_cold_load =
          (Result.Ok account, self_after) ->
        CanRead.t
          (interpreter :: self_after :: stack)%stack
          account
          ref_account ->
        exists
          (ref_account_info : '& AccountInfo.t)
          (ref_bytecode : '& Bytecode.t),
          {{
            SimulateM.eval_f
              (Impl_Deref_for_AccountInfoLoad.run_deref ref_account)
              (interpreter :: self_after :: stack)%stack 🌲
            (
              Output.Success ref_account_info,
              (interpreter :: self_after :: stack)%stack
            )
          }} /\
          {{
            SimulateM.eval_f
              (option.Impl_Option.run_as_ref
                {|
                  Ref.core :=
                    SubPointer.Runner.apply
                      ref_account_info.(Ref.core)
                      AccountInfo.SubPointer.get_code;
                |})
              (interpreter :: self_after :: stack)%stack 🌲
            (
              Output.Success (Some ref_bytecode),
              (interpreter :: self_after :: stack)%stack
            )
          }} /\
          {{
            SimulateM.eval_f
              (bytecode.Impl_Bytecode.run_len ref_bytecode)
              (interpreter :: self_after :: stack)%stack 🌲
            (
              Output.Success
                (bytes.simulate.bytes.Impl_Bytes.len
                  (account_info_load_original_bytes account).(Bytes.value)),
              (interpreter :: self_after :: stack)%stack
            )
          }};
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
      load_account_code
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (address : Address.t)
          (stack : Stack.t) :
        let ref_self : '&mut Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_load_account_code ref_self address)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(load_account_code) self address in
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
      max_initcode_size
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (stack : Stack.t) :
        let ref_self : '& Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_max_initcode_size ref_self)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(max_initcode_size) self in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }};
      beneficiary
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (stack : Stack.t) :
        let ref_self : '& Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_beneficiary ref_self)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(beneficiary) self in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }};
      block_number
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (stack : Stack.t) :
        let ref_self : '& Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_block_number ref_self)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(block_number) self in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }};
      timestamp
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (stack : Stack.t) :
        let ref_self : '& Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_timestamp ref_self)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(timestamp) self in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }};
      gas_limit
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (stack : Stack.t) :
        let ref_self : '& Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_gas_limit ref_self)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(gas_limit) self in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }};
      chain_id
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (stack : Stack.t) :
        let ref_self : '& Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_chain_id ref_self)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(chain_id) self in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }};
      basefee
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (stack : Stack.t) :
        let ref_self : '& Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_basefee ref_self)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(basefee) self in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }};
      blob_gasprice
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (stack : Stack.t) :
        let ref_self : '& Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_blob_gasprice ref_self)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(blob_gasprice) self in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }};
      effective_gas_price
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (stack : Stack.t) :
        let ref_self : '& Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_effective_gas_price ref_self)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(effective_gas_price) self in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }};
      caller
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (stack : Stack.t) :
        let ref_self : '& Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_caller ref_self)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(caller) self in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }};
      blob_hash
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (number : usize)
          (stack : Stack.t) :
        let ref_self : '& Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_blob_hash ref_self number)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(blob_hash) self number in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }};
      difficulty
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (stack : Stack.t) :
        let ref_self : '& Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_difficulty ref_self)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(difficulty) self in
          (
            Output.Success (fst result_self),
            (interpreter :: snd result_self :: stack)%stack
          )
        }};
      prevrandao
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (stack : Stack.t) :
        let ref_self : '& Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_prevrandao ref_self)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(prevrandao) self in
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
      sload_skip_cold_load
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (address : Address.t)
          (key : aliases.U256.t)
          (skip_cold_load : bool)
          (stack : Stack.t) :
        let ref_self : '&mut Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_sload_skip_cold_load ref_self address key skip_cold_load)
            (interpreter :: self :: stack)%stack 🌲
          let result_self := I.(sload_skip_cold_load) self address key skip_cold_load in
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
      sstore_skip_cold_load
          {Interpreter : Set}
          (interpreter : Interpreter)
          (self : Self)
          (address : Address.t)
          (key : aliases.U256.t)
          (value : aliases.U256.t)
          (skip_cold_load : bool)
          (stack : Stack.t) :
        let ref_self : '&mut Self := make_ref 1 in
        {{
          SimulateM.eval_f
            (Host.run_sstore_skip_cold_load ref_self address key value skip_cold_load)
            (interpreter :: self :: stack)%stack 🌲
          let result_self :=
            I.(sstore_skip_cold_load) self address key value skip_cold_load in
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

Lemma read_of_can_read
    {R A : Set} `{Link A}
    {kind : Pointer.Kind.t}
    (stack : Stack.t)
    (value : A)
    (ref_value : Ref.t kind A) :
  CanRead.t stack value ref_value ->
  {{
    SimulateM.read (R := R) stack ref_value.(Ref.core) 🌲
    Output.Success (R := R) value
  }}.
Proof.
  intros H_read.
  destruct H_read as [| ref_core H_access H_read]; cbn.
  { apply Run.Pure. }
  destruct H_access; cbn in H_read |- *.
  unshelve eapply Run.GetCanAccess.
  { econstructor; eassumption. }
  cbn.
  rewrite H_read.
  apply Run.Pure.
Qed.

Lemma as_u64_saturated_macro_eq_at_stack
    (stack : Stack.t)
    (v : aliases.U256.t) :
  {{
    SimulateM.eval_f
      (Impl_Uint.run_as_limbs 256 4 (Ref.immediate Pointer.Kind.Ref v))
      stack 🌲
    (
      Output.Success (Ref.immediate _ (Impl_Uint.as_limbs v)),
      stack
    )
  }}.
Proof.
  eapply Impl_Uint.as_limbs_eq.
  constructor.
Qed.

Lemma block_hash_eval_eq
    {Self Interpreter : Set} `{Link Self}
    {types : Host.Types.t} `{Host.Types.AreLinks types}
    `{run_Host_for_Self : !Host.Run Self types}
    `{IHost : !Host.C Self types}
    `{HostEq : !Host.Eq.t IHost}
    (interpreter : Interpreter)
    (self : Self)
    (ref_self : '&mut Self)
    (number : u64)
    (stack : Stack.t) :
  ref_self = make_ref 1 ->
  {{
    SimulateM.eval
      (links.M.evaluate
        (Host.run_block_hash
          (Ref.cast_to Pointer.Kind.MutRef ref_self)
          number).(Run.run_f))
      (interpreter :: self :: stack)%stack 🌲
    (
      Output.Success
        (fst (IHost.(Host.block_hash) self number)),
      (interpreter ::
        snd (IHost.(Host.block_hash) self number) ::
        stack)%stack
    )
  }}.
Proof.
  intros H_ref_self.
  subst ref_self.
  change (Ref.cast_to Pointer.Kind.MutRef (make_ref 1 : '&mut Self))
    with (make_ref 1 : '&mut Self).
  pose proof
    (HostEq.(Host.Eq.block_hash) interpreter self number stack) as H_block_hash.
  cbn [SimulateM.eval_f] in H_block_hash.
  exact H_block_hash.
Qed.
