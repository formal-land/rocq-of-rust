From Stdlib Require Import List ZArith.

Require Import RocqOfRust.RocqOfRust.
Require Import alloc.links.raw_vec.
Require Import alloc.vec.links.mod.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed_FixedBytes.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.links.common.
Require Import alloy_primitives.utils.simulate.keccak256.
Require Import alloy_primitives.log.links.mod.
Require Import bytes.links.bytes.
Require Import core.links.result.
Require Import links.M.
Require Import revm.revm_bytecode.links.bytecode.
Require Import revm.revm_context_interface.links.cfg.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.links.transaction.
Require Import revm.revm_context_interface.simulate.block.
Require Import revm.revm_context_interface.simulate.cfg.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_context_interface.simulate.transaction.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.lib.
Require Import simulate.M.

Import ListNotations.

Open Scope Z_scope.
Open Scope pstring_scope.

(** Stateful host used to execute interpreter programs against an explicit
    environment and account model. *)
Module StatefulHost.
  Module Environment.
    Module Block.
      Record t : Set := {
        coinbase : Z;
        gas_limit : Z;
        number : Z;
        timestamp : Z;
        difficulty : Z;
        base_fee : Z;
        blob_base_fee : Z;
        previous_randao : option Z;
        hashes : list (Z * Z);
        use_state_test_hashes : bool;
      }.
    End Block.

    Module Transaction.
      Record t : Set := {
        chain_id : Z;
        gas_price : Z;
        blob_hashes : list Z;
      }.
    End Transaction.

    Module Call.
      Record t : Set := {
        caller : Z;
      }.
    End Call.
  End Environment.

  Module Account.
    Record t : Set := {
      address : Z;
      balance : Z;
      nonce : Z;
      code : list Z;
      code_hash : Z;
      storage : list (Z * Z);
      transient_storage : list (Z * Z);
    }.
  End Account.

  Module EvmLog.
    Record t : Set := {
      address : Z;
      topics : list Z;
      data : list Z;
    }.
  End EvmLog.

  Module Change.
    Inductive t : Set :=
    | Balance (address value : Z)
    | Nonce (address nonce : Z)
    | Code (address : Z) (code : list Z)
    | Storage (address key value : Z)
    | TransientStorage (address key value : Z)
    | Created (address : Z)
    | SelfDestruct (address : Z).
  End Change.

  (** Keep changes newest-first for constant-time append. The two address
      indexes answer existential queries without rescanning a long journal.
      [to_list] restores chronological order at the observation boundary. *)
  Module Journal.
    (** Binary trie keyed by the bits of an injective Z-to-positive encoding.
        Membership and insertion depend on address bit width, not log length. *)
    Module AddressSet.
      Inductive t : Set :=
      | Empty
      | Node (present : bool) (even odd : t).

      Definition empty : t := Empty.

      Definition key (address : Z) : positive :=
        match address with
        | Z0 => xH
        | Zpos bits => xO bits
        | Zneg bits => xI bits
        end.

      Fixpoint mem_positive (bits : positive) (set : t) {struct bits} : bool :=
        match set with
        | Empty => false
        | Node present even odd =>
            match bits with
            | xH => present
            | xO rest => mem_positive rest even
            | xI rest => mem_positive rest odd
            end
        end.

      Fixpoint add_positive (bits : positive) (set : t) {struct bits} : t :=
        match set with
        | Empty =>
            match bits with
            | xH => Node true Empty Empty
            | xO rest => Node false (add_positive rest Empty) Empty
            | xI rest => Node false Empty (add_positive rest Empty)
            end
        | Node present even odd =>
            match bits with
            | xH => Node true even odd
            | xO rest => Node present (add_positive rest even) odd
            | xI rest => Node present even (add_positive rest odd)
            end
        end.

      Definition mem (address : Z) (set : t) : bool :=
        mem_positive (key address) set.

      Definition add (address : Z) (set : t) : t :=
        if mem address set then set else add_positive (key address) set.
    End AddressSet.

    Record t : Set := {
      newest_first : list Change.t;
      created_addresses : AddressSet.t;
      selfdestructed_addresses : AddressSet.t;
    }.

    Definition empty : t := {|
      newest_first := [];
      created_addresses := AddressSet.empty;
      selfdestructed_addresses := AddressSet.empty;
    |}.

    Definition append (journal : t) (change : Change.t) : t := {|
      newest_first := change :: journal.(newest_first);
      created_addresses :=
        match change with
        | Change.Created address => AddressSet.add address journal.(created_addresses)
        | _ => journal.(created_addresses)
        end;
      selfdestructed_addresses :=
        match change with
        | Change.SelfDestruct address =>
            AddressSet.add address journal.(selfdestructed_addresses)
        | _ => journal.(selfdestructed_addresses)
        end;
    |}.

    Definition of_list (changes : list Change.t) : t :=
      List.fold_left append changes empty.

    Definition to_list (journal : t) : list Change.t :=
      List.rev journal.(newest_first).

    Definition was_created (address : Z) (journal : t) : bool :=
      AddressSet.mem address journal.(created_addresses).

    Definition was_selfdestructed (address : Z) (journal : t) : bool :=
      AddressSet.mem address journal.(selfdestructed_addresses).

    Lemma to_list_append (journal : t) (change : Change.t) :
      to_list (append journal change) = to_list journal ++ [change].
    Proof. destruct journal. reflexivity. Qed.
  End Journal.

  Module Input.
    Record t : Set := {
      block : Environment.Block.t;
      transaction : Environment.Transaction.t;
      call : Environment.Call.t;
      state : list Account.t;
    }.
  End Input.
Module RustBlock := revm.revm_context_interface.simulate.block.Block.
Module RustCfg := revm.revm_context_interface.simulate.cfg.Cfg.
Module RustCfgTypes := revm.revm_context_interface.links.cfg.Cfg.Types.
Module RustCfgGetterTypes :=
  revm.revm_context_interface.links.cfg.CfgGetter.Types.
Module RustTransaction :=
  revm.revm_context_interface.simulate.transaction.Transaction.
Module RustTransactionTypes :=
  revm.revm_context_interface.links.transaction.Transaction.Types.

  Record t : Set := {
    input : Input.t;
    spec_id : SpecId.t;
    accounts : list Account.t;
    accessed_accounts : list Z;
    accessed_storage : list (Z * Z);
    logs : list EvmLog.t;
    state_changes : Journal.t;
    touched_accounts : list Z;
  }.

  Definition make (input : Input.t) : t :=
    {| input := input;
       spec_id := SpecId.CANCUN;
       accounts := input.(Input.state);
       accessed_accounts := [];
       accessed_storage := [];
       logs := [];
       state_changes := Journal.empty;
       touched_accounts := [] |}.

  (** Touches are separate from the observable mutation trace. A zero-value
      transfer and a zero fee credit can touch an account without changing it. *)
  Definition touch_account (host : t) (address : Z) : t :=
    if List.existsb (Z.eqb address) host.(touched_accounts) then host
    else host <| touched_accounts := address :: host.(touched_accounts) |>.

  (** The historical RIPEMD-160 touch exception survives every frame rollback
      after Spurious Dragon. All account data, logs and ordinary touches still
      come from the checkpoint, including address 3's original balance. *)
  Definition rollback (checkpoint current : t) : t :=
    if Impl_SpecId.is_enabled_in current.(spec_id) SpecId.SPURIOUS_DRAGON &&
       List.existsb (Z.eqb 3) current.(touched_accounts)
    then touch_account checkpoint 3 else checkpoint.

  Definition observe_logs (host : t) : list EvmLog.t :=
    host.(logs).

  Definition observe_state_changes (host : t) : list Change.t :=
    Journal.to_list host.(state_changes).

  Global Instance IsLink : Link t :=
    {| Φ := Ty.path "revm::revm_interpreter::tests::StatefulHost";
       φ _ := Value.Tuple [] |}.

  Definition identity_ref : RefStub.t t t :=
    {| RefStub.path := [];
       RefStub.projection self := self;
       RefStub.injection _ value := value |}.

  Definition transaction_types : RustTransactionTypes.t :=
    {| RustTransactionTypes.TransactionError := t;
       RustTransactionTypes.TransactionType := t;
       RustTransactionTypes.AccessList := t;
       RustTransactionTypes.Legacy := t;
       RustTransactionTypes.Eip2930 := t;
       RustTransactionTypes.Eip1559 := t;
       RustTransactionTypes.Eip4844 := t;
       RustTransactionTypes.Eip7702 := t |}.

  Global Instance TransactionTypesAreLinks :
      RustTransactionTypes.AreLinks transaction_types := {}.

  Definition host_types : Host.Types.t :=
    {| Host.Types.Transaction := t;
       Host.Types.TransactionTypes := transaction_types;
       Host.Types.Cfg := t;
       Host.Types.Spec := t;
       Host.Types.Block := t |}.

  Global Instance HostTypesAreLinks : Host.Types.AreLinks host_types := {}.

  Global Instance CfgTypesAreLinks :
      RustCfgTypes.AreLinks
        (RustCfgGetterTypes.to_Cfg_types
          (Host.Types.to_CfgGetter_types host_types)) := {}.

  Global Instance TransactionForHost :
      @RustTransaction.C
        t IsLink transaction_types TransactionTypesAreLinks.
  Proof.
    unshelve econstructor.
    - exact (fun self => self).
    - exact identity_ref.
    - exact identity_ref.
    - exact identity_ref.
    - exact identity_ref.
    - exact identity_ref.
    - exact (fun self =>
        {| M.Integer.value :=
             self.(input).(Input.transaction).(Environment.Transaction.gas_price) |}).
    - exact (fun self _ =>
        {| M.Integer.value :=
             self.(input).(Input.transaction).(Environment.Transaction.gas_price) |}).
    - exact (fun _ => TxKind.Create).
    - exact (fun _ => None).
  Defined.

  Global Instance TransactionGetterForHost :
      TransactionGetter.C t t transaction_types :=
    {| TransactionGetter.Transaction_for_Transaction := TransactionForHost;
       TransactionGetter.tx := (identity_ref : RefStub.t t t) |}.

  Global Instance BlockForHost : RustBlock.C t :=
    {| RustBlock.number self :=
         {| M.Integer.value :=
              self.(input).(Input.block).(Environment.Block.number) |};
       RustBlock.beneficiary self :=
         {| Address.value :=
              self.(input).(Input.block).(Environment.Block.coinbase) |};
       RustBlock.timestamp self :=
         {| M.Integer.value :=
              self.(input).(Input.block).(Environment.Block.timestamp) |};
       RustBlock.gas_limit self :=
         {| M.Integer.value :=
              self.(input).(Input.block).(Environment.Block.gas_limit) |};
       RustBlock.basefee self :=
         {| M.Integer.value :=
              self.(input).(Input.block).(Environment.Block.base_fee) |};
       RustBlock.difficulty self :=
         {| Uint.value :=
              self.(input).(Input.block).(Environment.Block.difficulty) |};
       RustBlock.prevrandao self :=
         match self.(input).(Input.block).(Environment.Block.previous_randao) with
         | Some value =>
             Some
               (Impl_From_U256_for_FixedBytes_32.from
                 {| Uint.value := value |})
         | None => None
         end;
       RustBlock.blob_excess_gas_and_price _ := None;
       RustBlock.blob_gasprice self :=
         Some
           {| M.Integer.value :=
                self.(input).(Input.block).(Environment.Block.blob_base_fee) |};
       RustBlock.blob_excess_gas _ := None |}.

  Global Instance BlockGetterForHost :
      BlockGetter.C t (Host.Types.to_BlockGetter_types host_types) :=
    {| BlockGetter.Block_for_Block := BlockForHost;
       BlockGetter.block := (identity_ref : RefStub.t t t) |}.

  Global Instance CfgForHost :
      @RustCfg.C
        t IsLink
        (RustCfgGetterTypes.to_Cfg_types
          (Host.Types.to_CfgGetter_types host_types))
        CfgTypesAreLinks.
  Proof.
    constructor.
    - exact (fun self =>
        {| M.Integer.value :=
             self.(input).(Input.transaction).(Environment.Transaction.chain_id) |}).
    - exact (fun self => self).
    - exact (fun _ => {| M.Integer.value := 24576 |}).
    - exact (fun _ => false).
    - exact (fun _ => false).
    - exact (fun _ => false).
    - exact (fun _ => false).
    - exact (fun _ => false).
    - exact (fun _ => false).
  Defined.

  Global Instance CfgGetterForHost :
      CfgGetter.C t (Host.Types.to_CfgGetter_types host_types) :=
    {| CfgGetter.Cfg_for_Cfg := CfgForHost;
       CfgGetter.cfg := (identity_ref : RefStub.t t t) |}.

  Definition append_change (host : t) (change : Change.t) : t :=
    {| input := host.(input);
       spec_id := host.(spec_id);
       accounts := host.(accounts);
       accessed_accounts := host.(accessed_accounts);
       accessed_storage := host.(accessed_storage);
       logs := host.(logs);
       state_changes := Journal.append host.(state_changes) change;
       touched_accounts := host.(touched_accounts) |}.

  Definition append_log (host : t) (entry : Log.t LogData.t) : t :=
    let data := entry.(Log.data) in
    {| input := host.(input);
       spec_id := host.(spec_id);
       accounts := host.(accounts);
       accessed_accounts := host.(accessed_accounts);
       accessed_storage := host.(accessed_storage);
       logs := host.(logs) ++
         [{| EvmLog.address := entry.(Log.address).(Address.value);
             EvmLog.topics :=
               List.map Uint.value data.(LogData.topics).(Vec.buf).(RawVec.value);
             EvmLog.data :=
               List.map M.Integer.value
                 data.(LogData.data)
                   .(alloy_primitives.bytes.links.mod.Bytes.value)
                   .(bytes.Bytes.value) |}];
       state_changes := host.(state_changes);
       touched_accounts := host.(touched_accounts) |}.

  Definition rust_address (value : Z) : Address.t :=
    {| Address.value := value |}.

  Definition rust_word (value : Z) : aliases.U256.t :=
    {| Uint.value := value |}.

  Definition rust_byte (value : Z) : u8 :=
    {| M.Integer.value := value |}.

  Fixpoint find_account
      (address : Z) (accounts : list Account.t) :
      option Account.t :=
    match accounts with
    | [] => None
    | account :: accounts =>
        if account.(Account.address) =? address
        then Some account
        else find_account address accounts
    end.

  Fixpoint lookup_word (key : Z) (entries : list (Z * Z)) : Z :=
    match entries with
    | [] => 0
    | (entry_key, value) :: entries =>
        if entry_key =? key then value else lookup_word key entries
    end.

  Fixpoint lookup_z (key : Z) (entries : list (Z * Z)) : option Z :=
    match entries with
    | [] => None
    | (entry_key, value) :: entries =>
        if entry_key =? key then Some value else lookup_z key entries
    end.

  Fixpoint update_word
      (key value : Z) (entries : list (Z * Z)) : list (Z * Z) :=
    match entries with
    | [] => [(key, value)]
    | (entry_key, entry_value) :: entries =>
        if entry_key =? key
        then (key, value) :: entries
        else (entry_key, entry_value) :: update_word key value entries
    end.

  Definition empty_code_hash : Z :=
    89477152217924674838424037953991966239322087453347756267410168184682657981552.

  Definition empty_account (address : Z) : Account.t :=
    {| Account.address := address;
       Account.balance := 0;
       Account.nonce := 0;
       Account.code := [];
       Account.code_hash := empty_code_hash;
       Account.storage := [];
       Account.transient_storage := [] |}.

  Definition account_with_storage
      (account : Account.t) (key value : Z) : Account.t :=
    {| Account.address := account.(Account.address);
       Account.balance := account.(Account.balance);
       Account.nonce := account.(Account.nonce);
       Account.code := account.(Account.code);
       Account.code_hash := account.(Account.code_hash);
       Account.storage := update_word key value account.(Account.storage);
       Account.transient_storage := account.(Account.transient_storage) |}.

  Definition account_with_transient_storage
      (account : Account.t) (key value : Z) : Account.t :=
    {| Account.address := account.(Account.address);
       Account.balance := account.(Account.balance);
       Account.nonce := account.(Account.nonce);
       Account.code := account.(Account.code);
       Account.code_hash := account.(Account.code_hash);
       Account.storage := account.(Account.storage);
       Account.transient_storage :=
         update_word key value account.(Account.transient_storage) |}.

  Definition account_with_balance
      (account : Account.t) (balance : Z) : Account.t :=
    {| Account.address := account.(Account.address);
       Account.balance := balance;
       Account.nonce := account.(Account.nonce);
       Account.code := account.(Account.code);
       Account.code_hash := account.(Account.code_hash);
       Account.storage := account.(Account.storage);
       Account.transient_storage := account.(Account.transient_storage) |}.

  Fixpoint update_account
      (address : Z)
      (update : Account.t -> Account.t)
      (accounts : list Account.t) : list Account.t :=
    match accounts with
    | [] => [update (empty_account address)]
    | account :: accounts =>
        if account.(Account.address) =? address
        then update account :: accounts
        else account :: update_account address update accounts
    end.

  Definition with_accounts (host : t) (accounts : list Account.t) : t :=
    {| input := host.(input);
       spec_id := host.(spec_id);
       accounts := accounts;
       accessed_accounts := host.(accessed_accounts);
       accessed_storage := host.(accessed_storage);
       logs := host.(logs);
       state_changes := host.(state_changes);
       touched_accounts := host.(touched_accounts) |}.

  Fixpoint storage_is_warm
      (address key : Z) (accessed_storage : list (Z * Z)) : bool :=
    match accessed_storage with
    | [] => false
    | (accessed_address, accessed_key) :: accessed_storage =>
        ((accessed_address =? address) && (accessed_key =? key)) ||
        storage_is_warm address key accessed_storage
    end.

  Definition storage_is_cold (host : t) (address key : Z) : bool :=
    negb (storage_is_warm address key host.(accessed_storage)).

  Definition mark_storage_warm (host : t) (address key : Z) : t :=
    if storage_is_warm address key host.(accessed_storage) then
      host
    else
      {| input := host.(input);
         spec_id := host.(spec_id);
         accounts := host.(accounts);
         accessed_accounts := host.(accessed_accounts);
         accessed_storage := (address, key) :: host.(accessed_storage);
         logs := host.(logs);
         state_changes := host.(state_changes);
         touched_accounts := host.(touched_accounts) |}.

  Definition balance (host : t) (address : Address.t) :
      option (StateLoad.t aliases.U256.t) * t :=
    let value :=
      match find_account address.(Address.value) host.(accounts) with
      | Some account => account.(Account.balance)
      | None => 0
      end in
    (Some {| StateLoad.data := rust_word value;
             StateLoad.is_cold := false |}, host).

  Definition account_is_empty (account : Account.t) : bool :=
    (account.(Account.balance) =? 0) &&
    (account.(Account.nonce) =? 0) &&
    match account.(Account.code) with
    | [] => true
    | _ => false
    end.

  Definition account_is_warm (host : t) (address : Z) : bool :=
    List.existsb (Z.eqb address) host.(accessed_accounts).

  Definition warm_account (host : t) (address : Z) : t :=
    if account_is_warm host address then host
    else
      {| input := host.(input);
         spec_id := host.(spec_id);
         accounts := host.(accounts);
         accessed_accounts := address :: host.(accessed_accounts);
         accessed_storage := host.(accessed_storage);
         logs := host.(logs);
         state_changes := host.(state_changes);
         touched_accounts := host.(touched_accounts) |}.

  Definition warm_access_list (host : t) (entries : list (Z * list Z)) : t :=
    List.fold_left
      (fun host entry =>
        let '(address, keys) := entry in
        List.fold_left
          (fun host key => mark_storage_warm host address key)
          keys (warm_account host address))
      entries host.

  (** Before EIP-161, an existing empty account is not a new account. *)
  Definition state_clear_aware_is_empty (host : t) (address : Z) : bool :=
    match find_account address host.(accounts) with
    | Some account =>
      Impl_SpecId.is_enabled_in host.(spec_id) SpecId.SPURIOUS_DRAGON && account_is_empty account
    | None =>
      Impl_SpecId.is_enabled_in host.(spec_id) SpecId.SPURIOUS_DRAGON ||
        negb (List.existsb (Z.eqb address) host.(touched_accounts))
    end.

  Definition account_info_load
      (host : t) (address : Address.t) (load_code : bool) : AccountInfoLoad.t :=
    let account :=
      match find_account address.(Address.value) host.(accounts) with
      | Some account => account
      | None => empty_account address.(Address.value)
      end in
    {| AccountInfoLoad.account :=
         Cow.Owned
           {| AccountInfo.balance := rust_word account.(Account.balance);
              AccountInfo.nonce :=
                {| M.Integer.value := account.(Account.nonce) |};
              AccountInfo.code_hash :=
                Impl_From_U256_for_FixedBytes_32.from
                  (rust_word account.(Account.code_hash));
              AccountInfo.code := if load_code then
                Some {| Bytecode.original_bytes :=
                  Impl_Bytes.copy_from_slice (List.map rust_byte account.(Account.code)) |}
                else None |};
       AccountInfoLoad.is_cold := negb (account_is_warm host address.(Address.value));
       AccountInfoLoad.is_empty := state_clear_aware_is_empty host address.(Address.value) |}.

  Definition load_account_info_skip_cold_load
      (host : t) (address : Address.t) (load_code skip_cold_load : bool) :
      Result.t AccountInfoLoad.t LoadError.t * t :=
    if skip_cold_load && negb (account_is_warm host address.(Address.value)) then
      (Result.Err LoadError.ColdLoadSkipped, host)
    else
      (Result.Ok (account_info_load host address load_code),
       warm_account host address.(Address.value)).

  Definition load_account_delegated
      (host : t) (address : Address.t) :
      option (StateLoad.t AccountLoad.t) * t :=
    let account :=
      match find_account address.(Address.value) host.(accounts) with
      | Some account => account
      | None => empty_account address.(Address.value)
      end in
    (Some
      {| StateLoad.data :=
           {| AccountLoad.is_delegate_account_cold := None;
              AccountLoad.is_empty := state_clear_aware_is_empty host address.(Address.value) |};
         StateLoad.is_cold := false |}, host).

  Definition code (host : t) (address : Address.t) :
      option
        (Eip7702CodeLoad.t alloy_primitives.bytes.links.mod.Bytes.t) * t :=
    let value :=
      match find_account address.(Address.value) host.(accounts) with
      | Some account => account.(Account.code)
      | None => []
      end in
    (Some
      {| Eip7702CodeLoad.state_load :=
           {| StateLoad.data :=
                Impl_Bytes.copy_from_slice (List.map rust_byte value);
              StateLoad.is_cold := false |};
         Eip7702CodeLoad.is_delegate_account_cold := None |}, host).

  Definition load_account_code (host : t) (address : Address.t) :
      option (StateLoad.t alloy_primitives.bytes.links.mod.Bytes.t) * t :=
    let value :=
      match find_account address.(Address.value) host.(accounts) with
      | Some account => account.(Account.code)
      | None => []
      end in
    (Some
      {| StateLoad.data :=
           Impl_Bytes.copy_from_slice (List.map rust_byte value);
         StateLoad.is_cold := false |}, host).

  Definition sload
      (host : t) (address : Address.t) (key : aliases.U256.t) :
      option (StateLoad.t aliases.U256.t) * t :=
    let address_value := address.(Address.value) in
    let key_value := key.(Uint.value) in
    let is_cold := storage_is_cold host address_value key_value in
    let value :=
      match find_account address_value host.(accounts) with
      | Some account => lookup_word key_value account.(Account.storage)
      | None => 0
      end in
    let host := mark_storage_warm host address_value key_value in
    (Some {| StateLoad.data := rust_word value;
             StateLoad.is_cold := is_cold |}, host).

  Definition code_hash (host : t) (address : Address.t) :
      option (Eip7702CodeLoad.t aliases.B256.t) * t :=
    let value :=
      match find_account address.(Address.value) host.(accounts) with
      | Some account => account.(Account.code_hash)
      | None => 0
      end in
    (Some
      {| Eip7702CodeLoad.state_load :=
           {| StateLoad.data :=
                Impl_From_U256_for_FixedBytes_32.from (rust_word value);
              StateLoad.is_cold := false |};
         Eip7702CodeLoad.is_delegate_account_cold := None |}, host).

  Definition sstore
      (host : t) (address : Address.t)
      (key value : aliases.U256.t) :
      option (StateLoad.t SStoreResult.t) * t :=
    let address_value := address.(Address.value) in
    let key_value := key.(Uint.value) in
    let new_value := value.(Uint.value) in
    let is_cold := storage_is_cold host address_value key_value in
    let present_value :=
      match find_account address_value host.(accounts) with
      | Some account => lookup_word key_value account.(Account.storage)
      | None => 0
      end in
    let original_value :=
      if Journal.was_created address_value host.(state_changes) then 0 else
      match find_account address_value host.(input).(Input.state) with
      | Some account => lookup_word key_value account.(Account.storage)
      | None => 0
      end in
    let accounts :=
      update_account address_value
        (fun account => account_with_storage account key_value new_value)
        host.(accounts) in
    let host := with_accounts host accounts in
    let host := mark_storage_warm host address_value key_value in
    let host := append_change host
      (Change.Storage address_value key_value new_value) in
    (Some
      {| StateLoad.data :=
           {| SStoreResult.original_value := rust_word original_value;
              SStoreResult.present_value := rust_word present_value;
              SStoreResult.new_value := value |};
         StateLoad.is_cold := is_cold |}, host).

  Definition tload
      (host : t) (address : Address.t) (key : aliases.U256.t) :
      aliases.U256.t * t :=
    let value :=
      match find_account address.(Address.value) host.(accounts) with
      | Some account =>
          lookup_word key.(Uint.value) account.(Account.transient_storage)
      | None => 0
      end in
    (rust_word value, host).

  Definition tstore
      (host : t) (address : Address.t)
      (key value : aliases.U256.t) : t :=
    let address_value := address.(Address.value) in
    let key_value := key.(Uint.value) in
    let new_value := value.(Uint.value) in
    let accounts :=
      update_account address_value
        (fun account =>
          account_with_transient_storage account key_value new_value)
        host.(accounts) in
    append_change (with_accounts host accounts)
      (Change.TransientStorage address_value key_value new_value).

  Definition sload_skip_cold_load
      (host : t) (address : Address.t) (key : aliases.U256.t)
      (skip_cold : bool) :
      Result.t (StateLoad.t aliases.U256.t) LoadError.t * t :=
    if skip_cold &&
       storage_is_cold host address.(Address.value) key.(Uint.value) then
      (Result.Err LoadError.ColdLoadSkipped, host)
    else
      let '(result, host) := sload host address key in
      (match result with
       | Some value => Result.Ok value
       | None => Result.Err LoadError.DBError
       end, host).

  Definition sstore_skip_cold_load
      (host : t) (address : Address.t)
      (key value : aliases.U256.t) (skip_cold : bool) :
      Result.t (StateLoad.t SStoreResult.t) LoadError.t * t :=
    if skip_cold &&
       storage_is_cold host address.(Address.value) key.(Uint.value) then
      (Result.Err LoadError.ColdLoadSkipped, host)
    else
      let '(result, host) := sstore host address key value in
      (match result with
       | Some value => Result.Ok value
       | None => Result.Err LoadError.DBError
       end, host).

  Definition was_selfdestructed
      (address : Z) (changes : Journal.t) : bool :=
    Journal.was_selfdestructed address changes.

  Definition selfdestruct
      (host : t) (address target : Address.t) (skip_cold : bool) :
      Result.t (StateLoad.t SelfDestructResult.t) LoadError.t * t :=
    let address_value := address.(Address.value) in
    let target_value := target.(Address.value) in
    let is_cold := negb (account_is_warm host target_value) in
    if skip_cold && is_cold then (Result.Err LoadError.ColdLoadSkipped, host) else
    let host := warm_account host target_value in
    let source :=
      match find_account address_value host.(accounts) with
      | Some account => account
      | None => empty_account address_value
      end in
    let target_exists :=
      match find_account target_value host.(accounts) with
      | Some account =>
          if Impl_SpecId.is_enabled_in host.(spec_id) SpecId.SPURIOUS_DRAGON
          then negb (account_is_empty account) else true
      | None => false
      end in
    let target_balance :=
      match find_account target_value host.(accounts) with
      | Some account => account.(Account.balance)
      | None => 0
      end in
    let previously_destroyed :=
      was_selfdestructed address_value host.(state_changes) in
    let created := Journal.was_created address_value host.(state_changes) in
    let destroys := created ||
      negb (Impl_SpecId.is_enabled_in host.(spec_id) SpecId.CANCUN) in
    let clears_balance := destroys || negb (address_value =? target_value) in
    let host := if address_value =? target_value then host
      else touch_account host target_value in
    let transferred_balance :=
      (target_balance + source.(Account.balance)) mod 2 ^ 256 in
    let accounts :=
      if clears_balance then update_account address_value
        (fun account => account_with_balance account 0)
        host.(accounts) else host.(accounts) in
    let accounts :=
      if address_value =? target_value
      then accounts
      else
        update_account target_value
          (fun account =>
            account_with_balance account transferred_balance)
          accounts in
    let host := with_accounts host accounts in
    let host := if clears_balance then append_change host
      (Change.Balance address_value 0) else host in
    let host :=
      if address_value =? target_value
      then host
      else append_change host
        (Change.Balance target_value
          transferred_balance) in
    let host := if destroys then
      append_change host (Change.SelfDestruct address_value) else host in
    (Result.Ok
      {| StateLoad.data :=
           {| SelfDestructResult.had_value :=
                negb (source.(Account.balance) =? 0);
              SelfDestructResult.target_exists := target_exists;
              SelfDestructResult.previously_destroyed :=
                previously_destroyed |};
         StateLoad.is_cold := is_cold |}, host).

  Definition finalize_selfdestructs (host : t) : t :=
    with_accounts host (List.filter
      (fun account => negb (was_selfdestructed account.(Account.address) host.(state_changes)))
      host.(accounts)).

  (** Geth's StateTestState supplies Keccak-256 of the decimal block number
      for a missing BLOCKHASH entry. Its [vmTestBlockHash] casts u64 to i64
      before decimal formatting. This is a fixture-host option, not a change
      to the REVM host's external-error behavior. *)
  Fixpoint decimal_digits (fuel : nat) (value : Z) : list Z :=
    match fuel with
    | O => []
    | S rest =>
        if value <? 10 then [48 + value]
        else decimal_digits rest (value / 10) ++ [48 + value mod 10]
    end.

  Definition state_test_block_hash (number : Z) : Z :=
    let signed := if number <? 2 ^ 63 then number else number - 2 ^ 64 in
    let decimal := if signed <? 0 then 45 :: decimal_digits 20 (-signed)
      else decimal_digits 20 signed in
    List.fold_left (fun value byte => 256 * value + byte)
      (Keccak256.hash decimal) 0.

  Definition block_hash (host : t) (number : u64) :
      option aliases.B256.t * t :=
    let block := host.(input).(Input.block) in
    let hash := match lookup_z number.(M.Integer.value)
      block.(Environment.Block.hashes) with
      | Some value => Some value
      | None => if block.(Environment.Block.use_state_test_hashes)
        then Some (state_test_block_hash number.(M.Integer.value)) else None
      end in
    (option_map
      (fun value =>
        Impl_From_U256_for_FixedBytes_32.from (rust_word value)) hash, host).

  Global Instance HostForRevmHost :
      @Host.C t IsLink host_types HostTypesAreLinks :=
    {| Host.TransactionGetter_for_Self := TransactionGetterForHost;
       Host.BlockGetter_for_Self := BlockGetterForHost;
       Host.CfgGetter_for_Self := CfgGetterForHost;
       Host.load_account_info_skip_cold_load self address load_code skip_cold_load :=
         load_account_info_skip_cold_load self address load_code skip_cold_load;
       Host.load_account_delegated := load_account_delegated;
       Host.load_account_code := load_account_code;
       Host.block_hash := block_hash;
       Host.max_initcode_size self :=
         ({| M.Integer.value := 49152 |}, self);
       Host.beneficiary self :=
         (rust_address self.(input).(Input.block).(Environment.Block.coinbase), self);
       Host.block_number self :=
         (rust_word self.(input).(Input.block).(Environment.Block.number), self);
       Host.timestamp self :=
         (rust_word self.(input).(Input.block).(Environment.Block.timestamp), self);
       Host.gas_limit self :=
         (rust_word self.(input).(Input.block).(Environment.Block.gas_limit), self);
       Host.chain_id self :=
         (rust_word
            self.(input).(Input.transaction).(Environment.Transaction.chain_id), self);
       Host.basefee self :=
         (rust_word self.(input).(Input.block).(Environment.Block.base_fee), self);
       Host.blob_gasprice self :=
         (rust_word self.(input).(Input.block).(Environment.Block.blob_base_fee), self);
       Host.effective_gas_price self :=
         (rust_word
            self.(input).(Input.transaction).(Environment.Transaction.gas_price), self);
       Host.caller self :=
         (rust_address self.(input).(Input.call).(Environment.Call.caller), self);
       Host.blob_hash self number :=
         let hashes :=
           self.(input).(Input.transaction).(Environment.Transaction.blob_hashes) in
         let index := number.(M.Integer.value) in
         (if (0 <=? index) && (index <? Z.of_nat (List.length hashes)) then
            option_map rust_word (nth_error hashes (Z.to_nat index))
          else None, self);
       Host.difficulty self :=
         (rust_word self.(input).(Input.block).(Environment.Block.difficulty), self);
       Host.prevrandao self :=
         (option_map rust_word
            self.(input).(Input.block).(Environment.Block.previous_randao), self);
       Host.balance := balance;
       Host.code := code;
       Host.code_hash := code_hash;
       Host.sload := sload;
       Host.sload_skip_cold_load self address key skip_cold :=
         sload_skip_cold_load self address key skip_cold;
       Host.sstore := sstore;
       Host.sstore_skip_cold_load self address key value skip_cold :=
         sstore_skip_cold_load self address key value skip_cold;
       Host.tload := tload;
       Host.tstore := tstore;
       Host.log self entry := append_log self entry;
       Host.selfdestruct self address target skip_cold :=
         selfdestruct self address target skip_cold |}.
End StatefulHost.
Export (hints) StatefulHost.
