(* Generated file. Do not edit. *)
Require Import links.RocqOfRust.
Require Import revm.links.dependencies.

Module Bytecode.
  Inductive t : Set :=
  | Eip7702
    (_ : eip7702.Eip7702Bytecode.t)
  | LegacyAnalyzed
    (_ : analyzed.LegacyAnalyzedBytecode.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::bytecode::Bytecode";
    φ x :=
      match x with
      | Eip7702 γ0 =>
        Value.StructTuple "revm_bytecode::bytecode::Bytecode::Eip7702" [
          φ γ0
        ]
      | LegacyAnalyzed γ0 =>
        Value.StructTuple "revm_bytecode::bytecode::Bytecode::LegacyAnalyzed" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_bytecode::bytecode::Bytecode").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Eip7702
    (γ0 : eip7702.Eip7702Bytecode.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_bytecode::bytecode::Bytecode::Eip7702" [
      γ0
    ] =
    φ (Eip7702 γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip7702 : of_value.

  Lemma of_value_with_LegacyAnalyzed
    (γ0 : analyzed.LegacyAnalyzedBytecode.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_bytecode::bytecode::Bytecode::LegacyAnalyzed" [
      γ0
    ] =
    φ (LegacyAnalyzed γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_LegacyAnalyzed : of_value.

  Definition of_value_Eip7702
    (γ0 : eip7702.Eip7702Bytecode.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_bytecode::bytecode::Bytecode::Eip7702" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Eip7702; eassumption. Defined.
  Smpl Add simple apply of_value_Eip7702 : of_value.

  Definition of_value_LegacyAnalyzed
    (γ0 : analyzed.LegacyAnalyzedBytecode.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_bytecode::bytecode::Bytecode::LegacyAnalyzed" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_LegacyAnalyzed; eassumption. Defined.
  Smpl Add simple apply of_value_LegacyAnalyzed : of_value.

  Module SubPointer.
    Definition get_Eip7702_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_bytecode::bytecode::Bytecode::Eip7702" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Eip7702 γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : eip7702.Eip7702Bytecode.t) :=
        match γ with
        | Eip7702 _ => Some (Eip7702 γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Eip7702_0_is_valid : SubPointer.Runner.Valid.t get_Eip7702_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Eip7702_0_is_valid : run_sub_pointer.

    Definition get_LegacyAnalyzed_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_bytecode::bytecode::Bytecode::LegacyAnalyzed" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | LegacyAnalyzed γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : analyzed.LegacyAnalyzedBytecode.t) :=
        match γ with
        | LegacyAnalyzed _ => Some (LegacyAnalyzed γ_0)
        | _ => None
        end;
    |}.

    Lemma get_LegacyAnalyzed_0_is_valid : SubPointer.Runner.Valid.t get_LegacyAnalyzed_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_LegacyAnalyzed_0_is_valid : run_sub_pointer.
  End SubPointer.
End Bytecode.

Module BytecodeDecodeError.
  Inductive t : Set :=
  | Eip7702
    (_ : eip7702.Eip7702DecodeError.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::decode_errors::BytecodeDecodeError";
    φ x :=
      match x with
      | Eip7702 γ0 =>
        Value.StructTuple "revm_bytecode::decode_errors::BytecodeDecodeError::Eip7702" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_bytecode::decode_errors::BytecodeDecodeError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Eip7702
    (γ0 : eip7702.Eip7702DecodeError.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_bytecode::decode_errors::BytecodeDecodeError::Eip7702" [
      γ0
    ] =
    φ (Eip7702 γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip7702 : of_value.

  Definition of_value_Eip7702
    (γ0 : eip7702.Eip7702DecodeError.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_bytecode::decode_errors::BytecodeDecodeError::Eip7702" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Eip7702; eassumption. Defined.
  Smpl Add simple apply of_value_Eip7702 : of_value.

  Module SubPointer.
    Definition get_Eip7702_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_bytecode::decode_errors::BytecodeDecodeError::Eip7702" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Eip7702 γ_0 => Some γ_0
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : eip7702.Eip7702DecodeError.t) :=
        match γ with
        | Eip7702 _ => Some (Eip7702 γ_0)
        end;
    |}.

    Lemma get_Eip7702_0_is_valid : SubPointer.Runner.Valid.t get_Eip7702_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Eip7702_0_is_valid : run_sub_pointer.
  End SubPointer.
End BytecodeDecodeError.

Module Eip7702Bytecode.
  Record t : Set := {
    delegated_address: address.Address.t;
    version: U8.t;
    raw: bytes_.Bytes.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eip7702::Eip7702Bytecode";
    φ '(Build_t delegated_address version raw) :=
      Value.StructRecord "revm_bytecode::eip7702::Eip7702Bytecode" [
        ("delegated_address", φ delegated_address);
        ("version", φ version);
        ("raw", φ raw)
      ]
  }.
End Eip7702Bytecode.

Module Eip7702DecodeError.
  Inductive t : Set :=
  | InvalidLength
  | InvalidMagic
  | UnsupportedVersion
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eip7702::Eip7702DecodeError";
    φ x :=
      match x with
      | InvalidLength =>
        Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::InvalidLength" []
      | InvalidMagic =>
        Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::InvalidMagic" []
      | UnsupportedVersion =>
        Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::UnsupportedVersion" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_bytecode::eip7702::Eip7702DecodeError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_InvalidLength :
    Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::InvalidLength" [] =
    φ InvalidLength.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidLength : of_value.

  Lemma of_value_with_InvalidMagic :
    Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::InvalidMagic" [] =
    φ InvalidMagic.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidMagic : of_value.

  Lemma of_value_with_UnsupportedVersion :
    Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::UnsupportedVersion" [] =
    φ UnsupportedVersion.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_UnsupportedVersion : of_value.

  Definition of_value_InvalidLength :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::InvalidLength" []
    ).
  Proof. econstructor; apply of_value_with_InvalidLength; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidLength : of_value.

  Definition of_value_InvalidMagic :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::InvalidMagic" []
    ).
  Proof. econstructor; apply of_value_with_InvalidMagic; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidMagic : of_value.

  Definition of_value_UnsupportedVersion :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::UnsupportedVersion" []
    ).
  Proof. econstructor; apply of_value_with_UnsupportedVersion; eassumption. Defined.
  Smpl Add simple apply of_value_UnsupportedVersion : of_value.

  Module SubPointer.

  End SubPointer.
End Eip7702DecodeError.

Module BytecodeIterator.
  Record t : Set := {
    bytes: iter.Iter.t U8.t;
    start: '*const U8.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::iter::BytecodeIterator";
    φ '(Build_t bytes start) :=
      Value.StructRecord "revm_bytecode::iter::BytecodeIterator" [
        ("bytes", φ bytes);
        ("start", φ start)
      ]
  }.
End BytecodeIterator.

Module LegacyAnalyzedBytecode.
  Record t : Set := {
    bytecode: bytes_.Bytes.t;
    original_len: Usize.t;
    jump_table: jump_map.JumpTable.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::legacy::analyzed::LegacyAnalyzedBytecode";
    φ '(Build_t bytecode original_len jump_table) :=
      Value.StructRecord "revm_bytecode::legacy::analyzed::LegacyAnalyzedBytecode" [
        ("bytecode", φ bytecode);
        ("original_len", φ original_len);
        ("jump_table", φ jump_table)
      ]
  }.
End LegacyAnalyzedBytecode.

Module JumpTable.
  Record t : Set := {
    table_ptr: '*const U8.t;
    len: Usize.t;
    table: sync.Arc.t bytes_.Bytes.t alloc.Global.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::legacy::jump_map::JumpTable";
    φ '(Build_t table_ptr len table) :=
      Value.StructRecord "revm_bytecode::legacy::jump_map::JumpTable" [
        ("table_ptr", φ table_ptr);
        ("len", φ len);
        ("table", φ table)
      ]
  }.
End JumpTable.

Module BlockEnv.
  Record t : Set := {
    number: ruint.Uint.t 256 4;
    beneficiary: address.Address.t;
    timestamp: ruint.Uint.t 256 4;
    gas_limit: U64.t;
    basefee: U64.t;
    difficulty: ruint.Uint.t 256 4;
    prevrandao: option.Option.t (fixed.FixedBytes.t 32);
    blob_excess_gas_and_price: option.Option.t blob.BlobExcessGasAndPrice.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context::block::BlockEnv";
    φ '(Build_t number beneficiary timestamp gas_limit basefee difficulty prevrandao blob_excess_gas_and_price) :=
      Value.StructRecord "revm_context::block::BlockEnv" [
        ("number", φ number);
        ("beneficiary", φ beneficiary);
        ("timestamp", φ timestamp);
        ("gas_limit", φ gas_limit);
        ("basefee", φ basefee);
        ("difficulty", φ difficulty);
        ("prevrandao", φ prevrandao);
        ("blob_excess_gas_and_price", φ blob_excess_gas_and_price)
      ]
  }.
End BlockEnv.

Module CfgEnv.
  Record t {SPEC: Set} : Set := {
    chain_id: U64.t;
    tx_chain_id_check: bool;
    spec: SPEC;
    limit_contract_code_size: option.Option.t Usize.t;
    limit_contract_initcode_size: option.Option.t Usize.t;
    disable_nonce_check: bool;
    max_blobs_per_tx: option.Option.t U64.t;
    blob_base_fee_update_fraction: option.Option.t U64.t;
    tx_gas_limit_cap: option.Option.t U64.t;
  }.
  Arguments Build_t {_}.
  Arguments t : clear implicits.

  Global Instance IsLink {SPEC: Set} `{Link SPEC} : Link (t SPEC) := {
    Φ := Ty.path "revm_context::cfg::CfgEnv";
    φ '(Build_t chain_id tx_chain_id_check spec limit_contract_code_size limit_contract_initcode_size disable_nonce_check max_blobs_per_tx blob_base_fee_update_fraction tx_gas_limit_cap) :=
      Value.StructRecord "revm_context::cfg::CfgEnv" [
        ("chain_id", φ chain_id);
        ("tx_chain_id_check", φ tx_chain_id_check);
        ("spec", φ spec);
        ("limit_contract_code_size", φ limit_contract_code_size);
        ("limit_contract_initcode_size", φ limit_contract_initcode_size);
        ("disable_nonce_check", φ disable_nonce_check);
        ("max_blobs_per_tx", φ max_blobs_per_tx);
        ("blob_base_fee_update_fraction", φ blob_base_fee_update_fraction);
        ("tx_gas_limit_cap", φ tx_gas_limit_cap)
      ]
  }.
End CfgEnv.

Module Context.
  Record t {BLOCK TX CFG DB JOURNAL CHAIN LOCAL: Set} : Set := {
    block: BLOCK;
    tx: TX;
    cfg: CFG;
    journaled_state: JOURNAL;
    chain: CHAIN;
    local: LOCAL;
    error: result.Result.t () (context.ContextError.t Unknown type {'AssociatedInTrait': {'trait_name': ['revm_database_interface', 'Database'], 'const_args': [], 'ty_args': [], 'self_ty': {'Var': {'name': 'DB'}}, 'name': 'Error'}});
  }.
  Arguments Build_t {_ _ _ _ _ _ _}.
  Arguments t : clear implicits.

  Global Instance IsLink {BLOCK TX CFG DB JOURNAL CHAIN LOCAL: Set} `{Link BLOCK} `{Link TX} `{Link CFG} `{Link DB} `{Link JOURNAL} `{Link CHAIN} `{Link LOCAL} : Link (t BLOCK TX CFG DB JOURNAL CHAIN LOCAL) := {
    Φ := Ty.path "revm_context::context::Context";
    φ '(Build_t block tx cfg journaled_state chain local error) :=
      Value.StructRecord "revm_context::context::Context" [
        ("block", φ block);
        ("tx", φ tx);
        ("cfg", φ cfg);
        ("journaled_state", φ journaled_state);
        ("chain", φ chain);
        ("local", φ local);
        ("error", φ error)
      ]
  }.
End Context.

Module Evm.
  Record t {CTX INSP I P F: Set} : Set := {
    ctx: CTX;
    inspector: INSP;
    instruction: I;
    precompiles: P;
    frame_stack: local.FrameStack.t F;
  }.
  Arguments Build_t {_ _ _ _ _}.
  Arguments t : clear implicits.

  Global Instance IsLink {CTX INSP I P F: Set} `{Link CTX} `{Link INSP} `{Link I} `{Link P} `{Link F} : Link (t CTX INSP I P F) := {
    Φ := Ty.path "revm_context::evm::Evm";
    φ '(Build_t ctx inspector instruction precompiles frame_stack) :=
      Value.StructRecord "revm_context::evm::Evm" [
        ("ctx", φ ctx);
        ("inspector", φ inspector);
        ("instruction", φ instruction);
        ("precompiles", φ precompiles);
        ("frame_stack", φ frame_stack)
      ]
  }.
End Evm.

Module Journal.
  Record t {DB ENTRY: Set} : Set := {
    database: DB;
    inner: inner.JournalInner.t ENTRY;
  }.
  Arguments Build_t {_ _}.
  Arguments t : clear implicits.

  Global Instance IsLink {DB ENTRY: Set} `{Link DB} `{Link ENTRY} : Link (t DB ENTRY) := {
    Φ := Ty.path "revm_context::journal::Journal";
    φ '(Build_t database inner) :=
      Value.StructRecord "revm_context::journal::Journal" [
        ("database", φ database);
        ("inner", φ inner)
      ]
  }.
End Journal.

Module LocalContext.
  Record t : Set := {
    shared_memory_buffer: rc.Rc.t (cell.RefCell.t (vec.Vec.t U8.t alloc.Global.t)) alloc.Global.t;
    precompile_error_message: option.Option.t string.String.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context::local::LocalContext";
    φ '(Build_t shared_memory_buffer precompile_error_message) :=
      Value.StructRecord "revm_context::local::LocalContext" [
        ("shared_memory_buffer", φ shared_memory_buffer);
        ("precompile_error_message", φ precompile_error_message)
      ]
  }.
End LocalContext.

Module TxEnv.
  Record t : Set := {
    tx_type: U8.t;
    caller: address.Address.t;
    gas_limit: U64.t;
    gas_price: U128.t;
    kind: common.TxKind.t;
    value: ruint.Uint.t 256 4;
    data: bytes_.Bytes.t;
    nonce: U64.t;
    chain_id: option.Option.t U64.t;
    access_list: alloy_eip2930.AccessList.t;
    gas_priority_fee: option.Option.t U128.t;
    blob_hashes: vec.Vec.t (fixed.FixedBytes.t 32) alloc.Global.t;
    max_fee_per_blob_gas: U128.t;
    authorization_list: vec.Vec.t (either.Either.t auth_list.SignedAuthorization.t auth_list.RecoveredAuthorization.t) alloc.Global.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context::tx::TxEnv";
    φ '(Build_t tx_type caller gas_limit gas_price kind value data nonce chain_id access_list gas_priority_fee blob_hashes max_fee_per_blob_gas authorization_list) :=
      Value.StructRecord "revm_context::tx::TxEnv" [
        ("tx_type", φ tx_type);
        ("caller", φ caller);
        ("gas_limit", φ gas_limit);
        ("gas_price", φ gas_price);
        ("kind", φ kind);
        ("value", φ value);
        ("data", φ data);
        ("nonce", φ nonce);
        ("chain_id", φ chain_id);
        ("access_list", φ access_list);
        ("gas_priority_fee", φ gas_priority_fee);
        ("blob_hashes", φ blob_hashes);
        ("max_fee_per_blob_gas", φ max_fee_per_blob_gas);
        ("authorization_list", φ authorization_list)
      ]
  }.
End TxEnv.

Module DeriveTxTypeError.
  Inductive t : Set :=
  | MissingTargetForEip4844
  | MissingTargetForEip7702
  | MissingTargetForEip7873
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context::tx::DeriveTxTypeError";
    φ x :=
      match x with
      | MissingTargetForEip4844 =>
        Value.StructTuple "revm_context::tx::DeriveTxTypeError::MissingTargetForEip4844" []
      | MissingTargetForEip7702 =>
        Value.StructTuple "revm_context::tx::DeriveTxTypeError::MissingTargetForEip7702" []
      | MissingTargetForEip7873 =>
        Value.StructTuple "revm_context::tx::DeriveTxTypeError::MissingTargetForEip7873" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context::tx::DeriveTxTypeError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_MissingTargetForEip4844 :
    Value.StructTuple "revm_context::tx::DeriveTxTypeError::MissingTargetForEip4844" [] =
    φ MissingTargetForEip4844.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MissingTargetForEip4844 : of_value.

  Lemma of_value_with_MissingTargetForEip7702 :
    Value.StructTuple "revm_context::tx::DeriveTxTypeError::MissingTargetForEip7702" [] =
    φ MissingTargetForEip7702.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MissingTargetForEip7702 : of_value.

  Lemma of_value_with_MissingTargetForEip7873 :
    Value.StructTuple "revm_context::tx::DeriveTxTypeError::MissingTargetForEip7873" [] =
    φ MissingTargetForEip7873.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MissingTargetForEip7873 : of_value.

  Definition of_value_MissingTargetForEip4844 :
    OfValue.t (
      Value.StructTuple "revm_context::tx::DeriveTxTypeError::MissingTargetForEip4844" []
    ).
  Proof. econstructor; apply of_value_with_MissingTargetForEip4844; eassumption. Defined.
  Smpl Add simple apply of_value_MissingTargetForEip4844 : of_value.

  Definition of_value_MissingTargetForEip7702 :
    OfValue.t (
      Value.StructTuple "revm_context::tx::DeriveTxTypeError::MissingTargetForEip7702" []
    ).
  Proof. econstructor; apply of_value_with_MissingTargetForEip7702; eassumption. Defined.
  Smpl Add simple apply of_value_MissingTargetForEip7702 : of_value.

  Definition of_value_MissingTargetForEip7873 :
    OfValue.t (
      Value.StructTuple "revm_context::tx::DeriveTxTypeError::MissingTargetForEip7873" []
    ).
  Proof. econstructor; apply of_value_with_MissingTargetForEip7873; eassumption. Defined.
  Smpl Add simple apply of_value_MissingTargetForEip7873 : of_value.

  Module SubPointer.

  End SubPointer.
End DeriveTxTypeError.

Module TxEnvBuilder.
  Record t : Set := {
    tx_type: option.Option.t U8.t;
    caller: address.Address.t;
    gas_limit: U64.t;
    gas_price: U128.t;
    kind: common.TxKind.t;
    value: ruint.Uint.t 256 4;
    data: bytes_.Bytes.t;
    nonce: U64.t;
    chain_id: option.Option.t U64.t;
    access_list: alloy_eip2930.AccessList.t;
    gas_priority_fee: option.Option.t U128.t;
    blob_hashes: vec.Vec.t (fixed.FixedBytes.t 32) alloc.Global.t;
    max_fee_per_blob_gas: U128.t;
    authorization_list: vec.Vec.t (either.Either.t auth_list.SignedAuthorization.t auth_list.RecoveredAuthorization.t) alloc.Global.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context::tx::TxEnvBuilder";
    φ '(Build_t tx_type caller gas_limit gas_price kind value data nonce chain_id access_list gas_priority_fee blob_hashes max_fee_per_blob_gas authorization_list) :=
      Value.StructRecord "revm_context::tx::TxEnvBuilder" [
        ("tx_type", φ tx_type);
        ("caller", φ caller);
        ("gas_limit", φ gas_limit);
        ("gas_price", φ gas_price);
        ("kind", φ kind);
        ("value", φ value);
        ("data", φ data);
        ("nonce", φ nonce);
        ("chain_id", φ chain_id);
        ("access_list", φ access_list);
        ("gas_priority_fee", φ gas_priority_fee);
        ("blob_hashes", φ blob_hashes);
        ("max_fee_per_blob_gas", φ max_fee_per_blob_gas);
        ("authorization_list", φ authorization_list)
      ]
  }.
End TxEnvBuilder.

Module TxEnvBuildError.
  Inductive t : Set :=
  | DeriveErr
    (_ : tx.DeriveTxTypeError.t)
  | MissingGasPriorityFeeForEip1559
  | MissingBlobHashesForEip4844
  | MissingAuthorizationListForEip7702
  | MissingTargetForEip4844
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context::tx::TxEnvBuildError";
    φ x :=
      match x with
      | DeriveErr γ0 =>
        Value.StructTuple "revm_context::tx::TxEnvBuildError::DeriveErr" [
          φ γ0
        ]
      | MissingGasPriorityFeeForEip1559 =>
        Value.StructTuple "revm_context::tx::TxEnvBuildError::MissingGasPriorityFeeForEip1559" []
      | MissingBlobHashesForEip4844 =>
        Value.StructTuple "revm_context::tx::TxEnvBuildError::MissingBlobHashesForEip4844" []
      | MissingAuthorizationListForEip7702 =>
        Value.StructTuple "revm_context::tx::TxEnvBuildError::MissingAuthorizationListForEip7702" []
      | MissingTargetForEip4844 =>
        Value.StructTuple "revm_context::tx::TxEnvBuildError::MissingTargetForEip4844" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context::tx::TxEnvBuildError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_DeriveErr
    (γ0 : tx.DeriveTxTypeError.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_context::tx::TxEnvBuildError::DeriveErr" [
      γ0
    ] =
    φ (DeriveErr γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_DeriveErr : of_value.

  Lemma of_value_with_MissingGasPriorityFeeForEip1559 :
    Value.StructTuple "revm_context::tx::TxEnvBuildError::MissingGasPriorityFeeForEip1559" [] =
    φ MissingGasPriorityFeeForEip1559.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MissingGasPriorityFeeForEip1559 : of_value.

  Lemma of_value_with_MissingBlobHashesForEip4844 :
    Value.StructTuple "revm_context::tx::TxEnvBuildError::MissingBlobHashesForEip4844" [] =
    φ MissingBlobHashesForEip4844.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MissingBlobHashesForEip4844 : of_value.

  Lemma of_value_with_MissingAuthorizationListForEip7702 :
    Value.StructTuple "revm_context::tx::TxEnvBuildError::MissingAuthorizationListForEip7702" [] =
    φ MissingAuthorizationListForEip7702.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MissingAuthorizationListForEip7702 : of_value.

  Lemma of_value_with_MissingTargetForEip4844 :
    Value.StructTuple "revm_context::tx::TxEnvBuildError::MissingTargetForEip4844" [] =
    φ MissingTargetForEip4844.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MissingTargetForEip4844 : of_value.

  Definition of_value_DeriveErr
    (γ0 : tx.DeriveTxTypeError.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_context::tx::TxEnvBuildError::DeriveErr" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_DeriveErr; eassumption. Defined.
  Smpl Add simple apply of_value_DeriveErr : of_value.

  Definition of_value_MissingGasPriorityFeeForEip1559 :
    OfValue.t (
      Value.StructTuple "revm_context::tx::TxEnvBuildError::MissingGasPriorityFeeForEip1559" []
    ).
  Proof. econstructor; apply of_value_with_MissingGasPriorityFeeForEip1559; eassumption. Defined.
  Smpl Add simple apply of_value_MissingGasPriorityFeeForEip1559 : of_value.

  Definition of_value_MissingBlobHashesForEip4844 :
    OfValue.t (
      Value.StructTuple "revm_context::tx::TxEnvBuildError::MissingBlobHashesForEip4844" []
    ).
  Proof. econstructor; apply of_value_with_MissingBlobHashesForEip4844; eassumption. Defined.
  Smpl Add simple apply of_value_MissingBlobHashesForEip4844 : of_value.

  Definition of_value_MissingAuthorizationListForEip7702 :
    OfValue.t (
      Value.StructTuple "revm_context::tx::TxEnvBuildError::MissingAuthorizationListForEip7702" []
    ).
  Proof. econstructor; apply of_value_with_MissingAuthorizationListForEip7702; eassumption. Defined.
  Smpl Add simple apply of_value_MissingAuthorizationListForEip7702 : of_value.

  Definition of_value_MissingTargetForEip4844 :
    OfValue.t (
      Value.StructTuple "revm_context::tx::TxEnvBuildError::MissingTargetForEip4844" []
    ).
  Proof. econstructor; apply of_value_with_MissingTargetForEip4844; eassumption. Defined.
  Smpl Add simple apply of_value_MissingTargetForEip4844 : of_value.

  Module SubPointer.
    Definition get_DeriveErr_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_context::tx::TxEnvBuildError::DeriveErr" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | DeriveErr γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : tx.DeriveTxTypeError.t) :=
        match γ with
        | DeriveErr _ => Some (DeriveErr γ_0)
        | _ => None
        end;
    |}.

    Lemma get_DeriveErr_0_is_valid : SubPointer.Runner.Valid.t get_DeriveErr_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_DeriveErr_0_is_valid : run_sub_pointer.
  End SubPointer.
End TxEnvBuildError.

Module JournalInner.
  Record t {ENTRY: Set} : Set := {
    state: map.HashMap.t address.Address.t revm_state.Account.t random.RandomState.t;
    transient_storage: map.HashMap.t (address.Address.t * (ruint.Uint.t 256 4)) (ruint.Uint.t 256 4) random.RandomState.t;
    logs: vec.Vec.t (log.Log.t log.LogData.t) alloc.Global.t;
    depth: Usize.t;
    journal: vec.Vec.t ENTRY alloc.Global.t;
    transaction_id: Usize.t;
    spec: hardfork.SpecId.t;
    warm_addresses: warm_addresses.WarmAddresses.t;
  }.
  Arguments Build_t {_}.
  Arguments t : clear implicits.

  Global Instance IsLink {ENTRY: Set} `{Link ENTRY} : Link (t ENTRY) := {
    Φ := Ty.path "revm_context::journal::inner::JournalInner";
    φ '(Build_t state transient_storage logs depth journal transaction_id spec warm_addresses) :=
      Value.StructRecord "revm_context::journal::inner::JournalInner" [
        ("state", φ state);
        ("transient_storage", φ transient_storage);
        ("logs", φ logs);
        ("depth", φ depth);
        ("journal", φ journal);
        ("transaction_id", φ transaction_id);
        ("spec", φ spec);
        ("warm_addresses", φ warm_addresses)
      ]
  }.
End JournalInner.

Module WarmAddresses.
  Record t : Set := {
    precompile_set: set.HashSet.t address.Address.t random.RandomState.t;
    precompile_short_addresses: vec.BitVec.t Usize.t order.Lsb0.t;
    precompile_all_short_addresses: bool;
    coinbase: option.Option.t address.Address.t;
    access_list: map.HashMap.t address.Address.t (set.HashSet.t (ruint.Uint.t 256 4) random.RandomState.t) random.RandomState.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context::journal::warm_addresses::WarmAddresses";
    φ '(Build_t precompile_set precompile_short_addresses precompile_all_short_addresses coinbase access_list) :=
      Value.StructRecord "revm_context::journal::warm_addresses::WarmAddresses" [
        ("precompile_set", φ precompile_set);
        ("precompile_short_addresses", φ precompile_short_addresses);
        ("precompile_all_short_addresses", φ precompile_all_short_addresses);
        ("coinbase", φ coinbase);
        ("access_list", φ access_list)
      ]
  }.
End WarmAddresses.

Module AnalysisKind.
  Inductive t : Set :=
  | Raw
  | Analyse
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::cfg::AnalysisKind";
    φ x :=
      match x with
      | Raw =>
        Value.StructTuple "revm_context_interface::cfg::AnalysisKind::Raw" []
      | Analyse =>
        Value.StructTuple "revm_context_interface::cfg::AnalysisKind::Analyse" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::cfg::AnalysisKind").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Raw :
    Value.StructTuple "revm_context_interface::cfg::AnalysisKind::Raw" [] =
    φ Raw.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Raw : of_value.

  Lemma of_value_with_Analyse :
    Value.StructTuple "revm_context_interface::cfg::AnalysisKind::Analyse" [] =
    φ Analyse.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Analyse : of_value.

  Definition of_value_Raw :
    OfValue.t (
      Value.StructTuple "revm_context_interface::cfg::AnalysisKind::Raw" []
    ).
  Proof. econstructor; apply of_value_with_Raw; eassumption. Defined.
  Smpl Add simple apply of_value_Raw : of_value.

  Definition of_value_Analyse :
    OfValue.t (
      Value.StructTuple "revm_context_interface::cfg::AnalysisKind::Analyse" []
    ).
  Proof. econstructor; apply of_value_with_Analyse; eassumption. Defined.
  Smpl Add simple apply of_value_Analyse : of_value.

  Module SubPointer.

  End SubPointer.
End AnalysisKind.

Module CreateScheme.
  Inductive t : Set :=
  | Create
  | Create2
    (salt : ruint.Uint.t 256 4)
  | Custom
    (address : address.Address.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::cfg::CreateScheme";
    φ x :=
      match x with
      | Create =>
        Value.StructTuple "revm_context_interface::cfg::CreateScheme::Create" []
      | Create2 salt =>
        Value.StructRecord "revm_context_interface::cfg::CreateScheme::Create2" [
          ("salt", φ salt)
        ]
      | Custom address =>
        Value.StructRecord "revm_context_interface::cfg::CreateScheme::Custom" [
          ("address", φ address)
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::cfg::CreateScheme").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Create :
    Value.StructTuple "revm_context_interface::cfg::CreateScheme::Create" [] =
    φ Create.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Create : of_value.

  Lemma of_value_with_Create2
    (salt : ruint.Uint.t 256 4) (salt' : Value.t) :
    salt' = φ salt ->
    Value.StructRecord "revm_context_interface::cfg::CreateScheme::Create2" [
      ("salt", salt')
    ] =
    φ (Create2 salt).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Create2 : of_value.

  Lemma of_value_with_Custom
    (address : address.Address.t) (address' : Value.t) :
    address' = φ address ->
    Value.StructRecord "revm_context_interface::cfg::CreateScheme::Custom" [
      ("address", address')
    ] =
    φ (Custom address).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Custom : of_value.

  Definition of_value_Create :
    OfValue.t (
      Value.StructTuple "revm_context_interface::cfg::CreateScheme::Create" []
    ).
  Proof. econstructor; apply of_value_with_Create; eassumption. Defined.
  Smpl Add simple apply of_value_Create : of_value.

  Definition of_value_Create2
    (salt : ruint.Uint.t 256 4) (salt' : Value.t) :
    salt' = φ salt ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::cfg::CreateScheme::Create2" [
        ("salt", salt')
      ]
    ).
  Proof. econstructor; apply of_value_with_Create2; eassumption. Defined.
  Smpl Add simple apply of_value_Create2 : of_value.

  Definition of_value_Custom
    (address : address.Address.t) (address' : Value.t) :
    address' = φ address ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::cfg::CreateScheme::Custom" [
        ("address", address')
      ]
    ).
  Proof. econstructor; apply of_value_with_Custom; eassumption. Defined.
  Smpl Add simple apply of_value_Custom : of_value.

  Module SubPointer.
    Definition get_Create2_salt : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::cfg::CreateScheme::Create2" "salt") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Create2 γ_salt => Some γ_salt
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_salt : ruint.Uint.t 256 4) :=
        match γ with
        | Create2 _ => Some (Create2 γ_salt)
        | _ => None
        end;
    |}.

    Lemma get_Create2_salt_is_valid : SubPointer.Runner.Valid.t get_Create2_salt.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Create2_salt_is_valid : run_sub_pointer.

    Definition get_Custom_address : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::cfg::CreateScheme::Custom" "address") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Custom γ_address => Some γ_address
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_address : address.Address.t) :=
        match γ with
        | Custom _ => Some (Custom γ_address)
        | _ => None
        end;
    |}.

    Lemma get_Custom_address_is_valid : SubPointer.Runner.Valid.t get_Custom_address.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Custom_address_is_valid : run_sub_pointer.
  End SubPointer.
End CreateScheme.

Module ContextError.
  Inductive t (DbError: Set) : Set :=
  | Db
    (_ : DbError)
  | Custom
    (_ : string.String.t)
  .
  Arguments Db Custom {_}.

  Global Instance IsLink (DbError: Set) : Link t DbError := {
    Φ := Ty.path "revm_context_interface::context::ContextError";
    φ x :=
      match x with
      | Db γ0 =>
        Value.StructTuple "revm_context_interface::context::ContextError::Db" [
          φ γ0
        ]
      | Custom γ0 =>
        Value.StructTuple "revm_context_interface::context::ContextError::Custom" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::context::ContextError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Db
    (γ0 : DbError) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_context_interface::context::ContextError::Db" [
      γ0
    ] =
    φ (Db γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Db : of_value.

  Lemma of_value_with_Custom
    (γ0 : string.String.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_context_interface::context::ContextError::Custom" [
      γ0
    ] =
    φ (Custom γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Custom : of_value.

  Definition of_value_Db
    (γ0 : DbError) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::context::ContextError::Db" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Db; eassumption. Defined.
  Smpl Add simple apply of_value_Db : of_value.

  Definition of_value_Custom
    (γ0 : string.String.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::context::ContextError::Custom" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Custom; eassumption. Defined.
  Smpl Add simple apply of_value_Custom : of_value.

  Module SubPointer.
    Definition get_Db_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_context_interface::context::ContextError::Db" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Db γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : DbError) :=
        match γ with
        | Db _ => Some (Db γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Db_0_is_valid : SubPointer.Runner.Valid.t get_Db_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Db_0_is_valid : run_sub_pointer.

    Definition get_Custom_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_context_interface::context::ContextError::Custom" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Custom γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : string.String.t) :=
        match γ with
        | Custom _ => Some (Custom γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Custom_0_is_valid : SubPointer.Runner.Valid.t get_Custom_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Custom_0_is_valid : run_sub_pointer.
  End SubPointer.
End ContextError.

Module SStoreResult.
  Record t : Set := {
    original_value: ruint.Uint.t 256 4;
    present_value: ruint.Uint.t 256 4;
    new_value: ruint.Uint.t 256 4;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::context::SStoreResult";
    φ '(Build_t original_value present_value new_value) :=
      Value.StructRecord "revm_context_interface::context::SStoreResult" [
        ("original_value", φ original_value);
        ("present_value", φ present_value);
        ("new_value", φ new_value)
      ]
  }.
End SStoreResult.

Module SelfDestructResult.
  Record t : Set := {
    had_value: bool;
    target_exists: bool;
    previously_destroyed: bool;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::context::SelfDestructResult";
    φ '(Build_t had_value target_exists previously_destroyed) :=
      Value.StructRecord "revm_context_interface::context::SelfDestructResult" [
        ("had_value", φ had_value);
        ("target_exists", φ target_exists);
        ("previously_destroyed", φ previously_destroyed)
      ]
  }.
End SelfDestructResult.

Module LoadError.
  Inductive t : Set :=
  | DBError
  | ColdLoadSkipped
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::host::LoadError";
    φ x :=
      match x with
      | DBError =>
        Value.StructTuple "revm_context_interface::host::LoadError::DBError" []
      | ColdLoadSkipped =>
        Value.StructTuple "revm_context_interface::host::LoadError::ColdLoadSkipped" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::host::LoadError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_DBError :
    Value.StructTuple "revm_context_interface::host::LoadError::DBError" [] =
    φ DBError.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_DBError : of_value.

  Lemma of_value_with_ColdLoadSkipped :
    Value.StructTuple "revm_context_interface::host::LoadError::ColdLoadSkipped" [] =
    φ ColdLoadSkipped.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ColdLoadSkipped : of_value.

  Definition of_value_DBError :
    OfValue.t (
      Value.StructTuple "revm_context_interface::host::LoadError::DBError" []
    ).
  Proof. econstructor; apply of_value_with_DBError; eassumption. Defined.
  Smpl Add simple apply of_value_DBError : of_value.

  Definition of_value_ColdLoadSkipped :
    OfValue.t (
      Value.StructTuple "revm_context_interface::host::LoadError::ColdLoadSkipped" []
    ).
  Proof. econstructor; apply of_value_with_ColdLoadSkipped; eassumption. Defined.
  Smpl Add simple apply of_value_ColdLoadSkipped : of_value.

  Module SubPointer.

  End SubPointer.
End LoadError.

Module JournalLoadError.
  Inductive t (E: Set) : Set :=
  | DBError
    (_ : E)
  | ColdLoadSkipped
  .
  Arguments DBError ColdLoadSkipped {_}.

  Global Instance IsLink (E: Set) : Link t E := {
    Φ := Ty.path "revm_context_interface::journaled_state::JournalLoadError";
    φ x :=
      match x with
      | DBError γ0 =>
        Value.StructTuple "revm_context_interface::journaled_state::JournalLoadError::DBError" [
          φ γ0
        ]
      | ColdLoadSkipped =>
        Value.StructTuple "revm_context_interface::journaled_state::JournalLoadError::ColdLoadSkipped" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::journaled_state::JournalLoadError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_DBError
    (γ0 : E) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_context_interface::journaled_state::JournalLoadError::DBError" [
      γ0
    ] =
    φ (DBError γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_DBError : of_value.

  Lemma of_value_with_ColdLoadSkipped :
    Value.StructTuple "revm_context_interface::journaled_state::JournalLoadError::ColdLoadSkipped" [] =
    φ ColdLoadSkipped.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ColdLoadSkipped : of_value.

  Definition of_value_DBError
    (γ0 : E) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::journaled_state::JournalLoadError::DBError" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_DBError; eassumption. Defined.
  Smpl Add simple apply of_value_DBError : of_value.

  Definition of_value_ColdLoadSkipped :
    OfValue.t (
      Value.StructTuple "revm_context_interface::journaled_state::JournalLoadError::ColdLoadSkipped" []
    ).
  Proof. econstructor; apply of_value_with_ColdLoadSkipped; eassumption. Defined.
  Smpl Add simple apply of_value_ColdLoadSkipped : of_value.

  Module SubPointer.
    Definition get_DBError_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_context_interface::journaled_state::JournalLoadError::DBError" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | DBError γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : E) :=
        match γ with
        | DBError _ => Some (DBError γ_0)
        | _ => None
        end;
    |}.

    Lemma get_DBError_0_is_valid : SubPointer.Runner.Valid.t get_DBError_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_DBError_0_is_valid : run_sub_pointer.
  End SubPointer.
End JournalLoadError.

Module TransferError.
  Inductive t : Set :=
  | OutOfFunds
  | OverflowPayment
  | CreateCollision
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::journaled_state::TransferError";
    φ x :=
      match x with
      | OutOfFunds =>
        Value.StructTuple "revm_context_interface::journaled_state::TransferError::OutOfFunds" []
      | OverflowPayment =>
        Value.StructTuple "revm_context_interface::journaled_state::TransferError::OverflowPayment" []
      | CreateCollision =>
        Value.StructTuple "revm_context_interface::journaled_state::TransferError::CreateCollision" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::journaled_state::TransferError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_OutOfFunds :
    Value.StructTuple "revm_context_interface::journaled_state::TransferError::OutOfFunds" [] =
    φ OutOfFunds.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfFunds : of_value.

  Lemma of_value_with_OverflowPayment :
    Value.StructTuple "revm_context_interface::journaled_state::TransferError::OverflowPayment" [] =
    φ OverflowPayment.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OverflowPayment : of_value.

  Lemma of_value_with_CreateCollision :
    Value.StructTuple "revm_context_interface::journaled_state::TransferError::CreateCollision" [] =
    φ CreateCollision.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateCollision : of_value.

  Definition of_value_OutOfFunds :
    OfValue.t (
      Value.StructTuple "revm_context_interface::journaled_state::TransferError::OutOfFunds" []
    ).
  Proof. econstructor; apply of_value_with_OutOfFunds; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfFunds : of_value.

  Definition of_value_OverflowPayment :
    OfValue.t (
      Value.StructTuple "revm_context_interface::journaled_state::TransferError::OverflowPayment" []
    ).
  Proof. econstructor; apply of_value_with_OverflowPayment; eassumption. Defined.
  Smpl Add simple apply of_value_OverflowPayment : of_value.

  Definition of_value_CreateCollision :
    OfValue.t (
      Value.StructTuple "revm_context_interface::journaled_state::TransferError::CreateCollision" []
    ).
  Proof. econstructor; apply of_value_with_CreateCollision; eassumption. Defined.
  Smpl Add simple apply of_value_CreateCollision : of_value.

  Module SubPointer.

  End SubPointer.
End TransferError.

Module JournalCheckpoint.
  Record t : Set := {
    log_i: Usize.t;
    journal_i: Usize.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::journaled_state::JournalCheckpoint";
    φ '(Build_t log_i journal_i) :=
      Value.StructRecord "revm_context_interface::journaled_state::JournalCheckpoint" [
        ("log_i", φ log_i);
        ("journal_i", φ journal_i)
      ]
  }.
End JournalCheckpoint.

Module StateLoad.
  Record t {T: Set} : Set := {
    data: T;
    is_cold: bool;
  }.
  Arguments Build_t {_}.
  Arguments t : clear implicits.

  Global Instance IsLink {T: Set} `{Link T} : Link (t T) := {
    Φ := Ty.path "revm_context_interface::journaled_state::StateLoad";
    φ '(Build_t data is_cold) :=
      Value.StructRecord "revm_context_interface::journaled_state::StateLoad" [
        ("data", φ data);
        ("is_cold", φ is_cold)
      ]
  }.
End StateLoad.

Module AccountLoad.
  Record t : Set := {
    is_delegate_account_cold: option.Option.t bool;
    is_empty: bool;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::journaled_state::AccountLoad";
    φ '(Build_t is_delegate_account_cold is_empty) :=
      Value.StructRecord "revm_context_interface::journaled_state::AccountLoad" [
        ("is_delegate_account_cold", φ is_delegate_account_cold);
        ("is_empty", φ is_empty)
      ]
  }.
End AccountLoad.

Module AccountInfoLoad.
  Record t : Set := {
    account: borrow.Cow.t account_info.AccountInfo.t;
    is_cold: bool;
    is_empty: bool;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::journaled_state::AccountInfoLoad";
    φ '(Build_t account is_cold is_empty) :=
      Value.StructRecord "revm_context_interface::journaled_state::AccountInfoLoad" [
        ("account", φ account);
        ("is_cold", φ is_cold);
        ("is_empty", φ is_empty)
      ]
  }.
End AccountInfoLoad.

Module FrameStack.
  Record t {T: Set} : Set := {
    stack: vec.Vec.t T alloc.Global.t;
    index: option.Option.t Usize.t;
  }.
  Arguments Build_t {_}.
  Arguments t : clear implicits.

  Global Instance IsLink {T: Set} `{Link T} : Link (t T) := {
    Φ := Ty.path "revm_context_interface::local::FrameStack";
    φ '(Build_t stack index) :=
      Value.StructRecord "revm_context_interface::local::FrameStack" [
        ("stack", φ stack);
        ("index", φ index)
      ]
  }.
End FrameStack.

Module OutFrame.
  Record t {T: Set} : Set := {
    ptr: '*mut T;
    init: bool;
    lt: marker.PhantomData.t ('&mut T);
  }.
  Arguments Build_t {_}.
  Arguments t : clear implicits.

  Global Instance IsLink {T: Set} `{Link T} : Link (t T) := {
    Φ := Ty.path "revm_context_interface::local::OutFrame";
    φ '(Build_t ptr init lt) :=
      Value.StructRecord "revm_context_interface::local::OutFrame" [
        ("ptr", φ ptr);
        ("init", φ init);
        ("lt", φ lt)
      ]
  }.
End OutFrame.

Module ExecResultAndState.
  Record t {R S: Set} : Set := {
    result: R;
    state: S;
  }.
  Arguments Build_t {_ _}.
  Arguments t : clear implicits.

  Global Instance IsLink {R S: Set} `{Link R} `{Link S} : Link (t R S) := {
    Φ := Ty.path "revm_context_interface::result::ExecResultAndState";
    φ '(Build_t result state) :=
      Value.StructRecord "revm_context_interface::result::ExecResultAndState" [
        ("result", φ result);
        ("state", φ state)
      ]
  }.
End ExecResultAndState.

Module ExecutionResult.
  Inductive t (HaltReasonTy: Set) : Set :=
  | Success
    (reason : result.SuccessReason.t)
    (gas_used : U64.t)
    (gas_refunded : U64.t)
    (logs : vec.Vec.t (log.Log.t log.LogData.t) alloc.Global.t)
    (output : result.Output.t)
  | Revert
    (gas_used : U64.t)
    (output : bytes_.Bytes.t)
  | Halt
    (reason : HaltReasonTy)
    (gas_used : U64.t)
  .
  Arguments Success Revert Halt {_}.

  Global Instance IsLink (HaltReasonTy: Set) : Link t HaltReasonTy := {
    Φ := Ty.path "revm_context_interface::result::ExecutionResult";
    φ x :=
      match x with
      | Success reason gas_used gas_refunded logs output =>
        Value.StructRecord "revm_context_interface::result::ExecutionResult::Success" [
          ("reason", φ reason);
          ("gas_used", φ gas_used);
          ("gas_refunded", φ gas_refunded);
          ("logs", φ logs);
          ("output", φ output)
        ]
      | Revert gas_used output =>
        Value.StructRecord "revm_context_interface::result::ExecutionResult::Revert" [
          ("gas_used", φ gas_used);
          ("output", φ output)
        ]
      | Halt reason gas_used =>
        Value.StructRecord "revm_context_interface::result::ExecutionResult::Halt" [
          ("reason", φ reason);
          ("gas_used", φ gas_used)
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::result::ExecutionResult").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Success
    (reason : result.SuccessReason.t) (reason' : Value.t)
    (gas_used : U64.t) (gas_used' : Value.t)
    (gas_refunded : U64.t) (gas_refunded' : Value.t)
    (logs : vec.Vec.t (log.Log.t log.LogData.t) alloc.Global.t) (logs' : Value.t)
    (output : result.Output.t) (output' : Value.t) :
    reason' = φ reason ->
    gas_used' = φ gas_used ->
    gas_refunded' = φ gas_refunded ->
    logs' = φ logs ->
    output' = φ output ->
    Value.StructRecord "revm_context_interface::result::ExecutionResult::Success" [
      ("reason", reason');
      ("gas_used", gas_used');
      ("gas_refunded", gas_refunded');
      ("logs", logs');
      ("output", output')
    ] =
    φ (Success reason gas_used gas_refunded logs output).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Success : of_value.

  Lemma of_value_with_Revert
    (gas_used : U64.t) (gas_used' : Value.t)
    (output : bytes_.Bytes.t) (output' : Value.t) :
    gas_used' = φ gas_used ->
    output' = φ output ->
    Value.StructRecord "revm_context_interface::result::ExecutionResult::Revert" [
      ("gas_used", gas_used');
      ("output", output')
    ] =
    φ (Revert gas_used output).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Revert : of_value.

  Lemma of_value_with_Halt
    (reason : HaltReasonTy) (reason' : Value.t)
    (gas_used : U64.t) (gas_used' : Value.t) :
    reason' = φ reason ->
    gas_used' = φ gas_used ->
    Value.StructRecord "revm_context_interface::result::ExecutionResult::Halt" [
      ("reason", reason');
      ("gas_used", gas_used')
    ] =
    φ (Halt reason gas_used).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Halt : of_value.

  Definition of_value_Success
    (reason : result.SuccessReason.t) (reason' : Value.t)
    (gas_used : U64.t) (gas_used' : Value.t)
    (gas_refunded : U64.t) (gas_refunded' : Value.t)
    (logs : vec.Vec.t (log.Log.t log.LogData.t) alloc.Global.t) (logs' : Value.t)
    (output : result.Output.t) (output' : Value.t) :
    reason' = φ reason ->
    gas_used' = φ gas_used ->
    gas_refunded' = φ gas_refunded ->
    logs' = φ logs ->
    output' = φ output ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::result::ExecutionResult::Success" [
        ("reason", reason');
        ("gas_used", gas_used');
        ("gas_refunded", gas_refunded');
        ("logs", logs');
        ("output", output')
      ]
    ).
  Proof. econstructor; apply of_value_with_Success; eassumption. Defined.
  Smpl Add simple apply of_value_Success : of_value.

  Definition of_value_Revert
    (gas_used : U64.t) (gas_used' : Value.t)
    (output : bytes_.Bytes.t) (output' : Value.t) :
    gas_used' = φ gas_used ->
    output' = φ output ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::result::ExecutionResult::Revert" [
        ("gas_used", gas_used');
        ("output", output')
      ]
    ).
  Proof. econstructor; apply of_value_with_Revert; eassumption. Defined.
  Smpl Add simple apply of_value_Revert : of_value.

  Definition of_value_Halt
    (reason : HaltReasonTy) (reason' : Value.t)
    (gas_used : U64.t) (gas_used' : Value.t) :
    reason' = φ reason ->
    gas_used' = φ gas_used ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::result::ExecutionResult::Halt" [
        ("reason", reason');
        ("gas_used", gas_used')
      ]
    ).
  Proof. econstructor; apply of_value_with_Halt; eassumption. Defined.
  Smpl Add simple apply of_value_Halt : of_value.

  Module SubPointer.
    Definition get_Success_reason : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::ExecutionResult::Success" "reason") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Success γ_reason _ _ _ _ => Some γ_reason
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_reason : result.SuccessReason.t) :=
        match γ with
        | Success _ γ_gas_used γ_gas_refunded γ_logs γ_output => Some (Success γ_reason γ_gas_used γ_gas_refunded γ_logs γ_output)
        | _ => None
        end;
    |}.

    Lemma get_Success_reason_is_valid : SubPointer.Runner.Valid.t get_Success_reason.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Success_reason_is_valid : run_sub_pointer.

    Definition get_Success_gas_used : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::ExecutionResult::Success" "gas_used") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Success _ γ_gas_used _ _ _ => Some γ_gas_used
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_gas_used : U64.t) :=
        match γ with
        | Success γ_reason _ γ_gas_refunded γ_logs γ_output => Some (Success γ_reason γ_gas_used γ_gas_refunded γ_logs γ_output)
        | _ => None
        end;
    |}.

    Lemma get_Success_gas_used_is_valid : SubPointer.Runner.Valid.t get_Success_gas_used.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Success_gas_used_is_valid : run_sub_pointer.

    Definition get_Success_gas_refunded : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::ExecutionResult::Success" "gas_refunded") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Success _ _ γ_gas_refunded _ _ => Some γ_gas_refunded
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_gas_refunded : U64.t) :=
        match γ with
        | Success γ_reason γ_gas_used _ γ_logs γ_output => Some (Success γ_reason γ_gas_used γ_gas_refunded γ_logs γ_output)
        | _ => None
        end;
    |}.

    Lemma get_Success_gas_refunded_is_valid : SubPointer.Runner.Valid.t get_Success_gas_refunded.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Success_gas_refunded_is_valid : run_sub_pointer.

    Definition get_Success_logs : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::ExecutionResult::Success" "logs") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Success _ _ _ γ_logs _ => Some γ_logs
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_logs : vec.Vec.t (log.Log.t log.LogData.t) alloc.Global.t) :=
        match γ with
        | Success γ_reason γ_gas_used γ_gas_refunded _ γ_output => Some (Success γ_reason γ_gas_used γ_gas_refunded γ_logs γ_output)
        | _ => None
        end;
    |}.

    Lemma get_Success_logs_is_valid : SubPointer.Runner.Valid.t get_Success_logs.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Success_logs_is_valid : run_sub_pointer.

    Definition get_Success_output : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::ExecutionResult::Success" "output") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Success _ _ _ _ γ_output => Some γ_output
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_output : result.Output.t) :=
        match γ with
        | Success γ_reason γ_gas_used γ_gas_refunded γ_logs _ => Some (Success γ_reason γ_gas_used γ_gas_refunded γ_logs γ_output)
        | _ => None
        end;
    |}.

    Lemma get_Success_output_is_valid : SubPointer.Runner.Valid.t get_Success_output.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Success_output_is_valid : run_sub_pointer.

    Definition get_Revert_gas_used : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::ExecutionResult::Revert" "gas_used") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Revert γ_gas_used _ => Some γ_gas_used
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_gas_used : U64.t) :=
        match γ with
        | Revert _ γ_output => Some (Revert γ_gas_used γ_output)
        | _ => None
        end;
    |}.

    Lemma get_Revert_gas_used_is_valid : SubPointer.Runner.Valid.t get_Revert_gas_used.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Revert_gas_used_is_valid : run_sub_pointer.

    Definition get_Revert_output : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::ExecutionResult::Revert" "output") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Revert _ γ_output => Some γ_output
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_output : bytes_.Bytes.t) :=
        match γ with
        | Revert γ_gas_used _ => Some (Revert γ_gas_used γ_output)
        | _ => None
        end;
    |}.

    Lemma get_Revert_output_is_valid : SubPointer.Runner.Valid.t get_Revert_output.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Revert_output_is_valid : run_sub_pointer.

    Definition get_Halt_reason : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::ExecutionResult::Halt" "reason") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Halt γ_reason _ => Some γ_reason
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_reason : HaltReasonTy) :=
        match γ with
        | Halt _ γ_gas_used => Some (Halt γ_reason γ_gas_used)
        | _ => None
        end;
    |}.

    Lemma get_Halt_reason_is_valid : SubPointer.Runner.Valid.t get_Halt_reason.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Halt_reason_is_valid : run_sub_pointer.

    Definition get_Halt_gas_used : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::ExecutionResult::Halt" "gas_used") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Halt _ γ_gas_used => Some γ_gas_used
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_gas_used : U64.t) :=
        match γ with
        | Halt γ_reason _ => Some (Halt γ_reason γ_gas_used)
        | _ => None
        end;
    |}.

    Lemma get_Halt_gas_used_is_valid : SubPointer.Runner.Valid.t get_Halt_gas_used.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Halt_gas_used_is_valid : run_sub_pointer.
  End SubPointer.
End ExecutionResult.

Module Output.
  Inductive t : Set :=
  | Call
    (_ : bytes_.Bytes.t)
  | Create
    (_ : bytes_.Bytes.t)
    (_ : option.Option.t address.Address.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::result::Output";
    φ x :=
      match x with
      | Call γ0 =>
        Value.StructTuple "revm_context_interface::result::Output::Call" [
          φ γ0
        ]
      | Create γ0 γ1 =>
        Value.StructTuple "revm_context_interface::result::Output::Create" [
          φ γ0;
          φ γ1
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::result::Output").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Call
    (γ0 : bytes_.Bytes.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_context_interface::result::Output::Call" [
      γ0
    ] =
    φ (Call γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Call : of_value.

  Lemma of_value_with_Create
    (γ0 : bytes_.Bytes.t) (γ0' : Value.t)
    (γ1 : option.Option.t address.Address.t) (γ1' : Value.t) :
    γ0' = φ γ0 ->
    γ1' = φ γ1 ->
    Value.StructTuple "revm_context_interface::result::Output::Create" [
      γ0;
      γ1
    ] =
    φ (Create γ0 γ1).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Create : of_value.

  Definition of_value_Call
    (γ0 : bytes_.Bytes.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::Output::Call" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Call; eassumption. Defined.
  Smpl Add simple apply of_value_Call : of_value.

  Definition of_value_Create
    (γ0 : bytes_.Bytes.t) (γ0' : Value.t)
    (γ1 : option.Option.t address.Address.t) (γ1' : Value.t) :
    γ0' = φ γ0 ->
    γ1' = φ γ1 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::Output::Create" [
        γ0;
        γ1
      ]
    ).
  Proof. econstructor; apply of_value_with_Create; eassumption. Defined.
  Smpl Add simple apply of_value_Create : of_value.

  Module SubPointer.
    Definition get_Call_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_context_interface::result::Output::Call" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Call γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : bytes_.Bytes.t) :=
        match γ with
        | Call _ => Some (Call γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Call_0_is_valid : SubPointer.Runner.Valid.t get_Call_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Call_0_is_valid : run_sub_pointer.

    Definition get_Create_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_context_interface::result::Output::Create" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Create γ_0 _ => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : bytes_.Bytes.t) :=
        match γ with
        | Create _ γ_1 => Some (Create γ_0 γ_1)
        | _ => None
        end;
    |}.

    Lemma get_Create_0_is_valid : SubPointer.Runner.Valid.t get_Create_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Create_0_is_valid : run_sub_pointer.

    Definition get_Create_1 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_context_interface::result::Output::Create" 1) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Create _ γ_1 => Some γ_1
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_1 : option.Option.t address.Address.t) :=
        match γ with
        | Create γ_0 _ => Some (Create γ_0 γ_1)
        | _ => None
        end;
    |}.

    Lemma get_Create_1_is_valid : SubPointer.Runner.Valid.t get_Create_1.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Create_1_is_valid : run_sub_pointer.
  End SubPointer.
End Output.

Module EVMError.
  Inductive t (DBError TransactionError: Set) : Set :=
  | Transaction
    (_ : TransactionError)
  | Header
    (_ : result.InvalidHeader.t)
  | Database
    (_ : DBError)
  | Custom
    (_ : string.String.t)
  .
  Arguments Transaction Header Database Custom {_ _}.

  Global Instance IsLink (DBError TransactionError: Set) : Link t DBError TransactionError := {
    Φ := Ty.path "revm_context_interface::result::EVMError";
    φ x :=
      match x with
      | Transaction γ0 =>
        Value.StructTuple "revm_context_interface::result::EVMError::Transaction" [
          φ γ0
        ]
      | Header γ0 =>
        Value.StructTuple "revm_context_interface::result::EVMError::Header" [
          φ γ0
        ]
      | Database γ0 =>
        Value.StructTuple "revm_context_interface::result::EVMError::Database" [
          φ γ0
        ]
      | Custom γ0 =>
        Value.StructTuple "revm_context_interface::result::EVMError::Custom" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::result::EVMError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Transaction
    (γ0 : TransactionError) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_context_interface::result::EVMError::Transaction" [
      γ0
    ] =
    φ (Transaction γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Transaction : of_value.

  Lemma of_value_with_Header
    (γ0 : result.InvalidHeader.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_context_interface::result::EVMError::Header" [
      γ0
    ] =
    φ (Header γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Header : of_value.

  Lemma of_value_with_Database
    (γ0 : DBError) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_context_interface::result::EVMError::Database" [
      γ0
    ] =
    φ (Database γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Database : of_value.

  Lemma of_value_with_Custom
    (γ0 : string.String.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_context_interface::result::EVMError::Custom" [
      γ0
    ] =
    φ (Custom γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Custom : of_value.

  Definition of_value_Transaction
    (γ0 : TransactionError) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::EVMError::Transaction" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Transaction; eassumption. Defined.
  Smpl Add simple apply of_value_Transaction : of_value.

  Definition of_value_Header
    (γ0 : result.InvalidHeader.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::EVMError::Header" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Header; eassumption. Defined.
  Smpl Add simple apply of_value_Header : of_value.

  Definition of_value_Database
    (γ0 : DBError) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::EVMError::Database" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Database; eassumption. Defined.
  Smpl Add simple apply of_value_Database : of_value.

  Definition of_value_Custom
    (γ0 : string.String.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::EVMError::Custom" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Custom; eassumption. Defined.
  Smpl Add simple apply of_value_Custom : of_value.

  Module SubPointer.
    Definition get_Transaction_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_context_interface::result::EVMError::Transaction" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Transaction γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : TransactionError) :=
        match γ with
        | Transaction _ => Some (Transaction γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Transaction_0_is_valid : SubPointer.Runner.Valid.t get_Transaction_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Transaction_0_is_valid : run_sub_pointer.

    Definition get_Header_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_context_interface::result::EVMError::Header" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Header γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : result.InvalidHeader.t) :=
        match γ with
        | Header _ => Some (Header γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Header_0_is_valid : SubPointer.Runner.Valid.t get_Header_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Header_0_is_valid : run_sub_pointer.

    Definition get_Database_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_context_interface::result::EVMError::Database" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Database γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : DBError) :=
        match γ with
        | Database _ => Some (Database γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Database_0_is_valid : SubPointer.Runner.Valid.t get_Database_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Database_0_is_valid : run_sub_pointer.

    Definition get_Custom_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_context_interface::result::EVMError::Custom" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Custom γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : string.String.t) :=
        match γ with
        | Custom _ => Some (Custom γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Custom_0_is_valid : SubPointer.Runner.Valid.t get_Custom_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Custom_0_is_valid : run_sub_pointer.
  End SubPointer.
End EVMError.

Module InvalidTransaction.
  Inductive t : Set :=
  | PriorityFeeGreaterThanMaxFee
  | GasPriceLessThanBasefee
  | CallerGasLimitMoreThanBlock
  | CallGasCostMoreThanGasLimit
    (initial_gas : U64.t)
    (gas_limit : U64.t)
  | GasFloorMoreThanGasLimit
    (gas_floor : U64.t)
    (gas_limit : U64.t)
  | RejectCallerWithCode
  | LackOfFundForMaxFee
    (fee : boxed.Box.t (ruint.Uint.t 256 4) alloc.Global.t)
    (balance : boxed.Box.t (ruint.Uint.t 256 4) alloc.Global.t)
  | OverflowPaymentInTransaction
  | NonceOverflowInTransaction
  | NonceTooHigh
    (tx : U64.t)
    (state : U64.t)
  | NonceTooLow
    (tx : U64.t)
    (state : U64.t)
  | CreateInitCodeSizeLimit
  | InvalidChainId
  | MissingChainId
  | TxGasLimitGreaterThanCap
    (gas_limit : U64.t)
    (cap : U64.t)
  | AccessListNotSupported
  | MaxFeePerBlobGasNotSupported
  | BlobVersionedHashesNotSupported
  | BlobGasPriceGreaterThanMax
    (block_blob_gas_price : U128.t)
    (tx_max_fee_per_blob_gas : U128.t)
  | EmptyBlobs
  | BlobCreateTransaction
  | TooManyBlobs
    (max : Usize.t)
    (have : Usize.t)
  | BlobVersionNotSupported
  | AuthorizationListNotSupported
  | AuthorizationListInvalidFields
  | EmptyAuthorizationList
  | Eip2930NotSupported
  | Eip1559NotSupported
  | Eip4844NotSupported
  | Eip7702NotSupported
  | Eip7873NotSupported
  | Eip7873MissingTarget
  | Str
    (_ : borrow.Cow.t str.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::result::InvalidTransaction";
    φ x :=
      match x with
      | PriorityFeeGreaterThanMaxFee =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::PriorityFeeGreaterThanMaxFee" []
      | GasPriceLessThanBasefee =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::GasPriceLessThanBasefee" []
      | CallerGasLimitMoreThanBlock =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::CallerGasLimitMoreThanBlock" []
      | CallGasCostMoreThanGasLimit initial_gas gas_limit =>
        Value.StructRecord "revm_context_interface::result::InvalidTransaction::CallGasCostMoreThanGasLimit" [
          ("initial_gas", φ initial_gas);
          ("gas_limit", φ gas_limit)
        ]
      | GasFloorMoreThanGasLimit gas_floor gas_limit =>
        Value.StructRecord "revm_context_interface::result::InvalidTransaction::GasFloorMoreThanGasLimit" [
          ("gas_floor", φ gas_floor);
          ("gas_limit", φ gas_limit)
        ]
      | RejectCallerWithCode =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::RejectCallerWithCode" []
      | LackOfFundForMaxFee fee balance =>
        Value.StructRecord "revm_context_interface::result::InvalidTransaction::LackOfFundForMaxFee" [
          ("fee", φ fee);
          ("balance", φ balance)
        ]
      | OverflowPaymentInTransaction =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::OverflowPaymentInTransaction" []
      | NonceOverflowInTransaction =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::NonceOverflowInTransaction" []
      | NonceTooHigh tx state =>
        Value.StructRecord "revm_context_interface::result::InvalidTransaction::NonceTooHigh" [
          ("tx", φ tx);
          ("state", φ state)
        ]
      | NonceTooLow tx state =>
        Value.StructRecord "revm_context_interface::result::InvalidTransaction::NonceTooLow" [
          ("tx", φ tx);
          ("state", φ state)
        ]
      | CreateInitCodeSizeLimit =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::CreateInitCodeSizeLimit" []
      | InvalidChainId =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::InvalidChainId" []
      | MissingChainId =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::MissingChainId" []
      | TxGasLimitGreaterThanCap gas_limit cap =>
        Value.StructRecord "revm_context_interface::result::InvalidTransaction::TxGasLimitGreaterThanCap" [
          ("gas_limit", φ gas_limit);
          ("cap", φ cap)
        ]
      | AccessListNotSupported =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::AccessListNotSupported" []
      | MaxFeePerBlobGasNotSupported =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::MaxFeePerBlobGasNotSupported" []
      | BlobVersionedHashesNotSupported =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobVersionedHashesNotSupported" []
      | BlobGasPriceGreaterThanMax block_blob_gas_price tx_max_fee_per_blob_gas =>
        Value.StructRecord "revm_context_interface::result::InvalidTransaction::BlobGasPriceGreaterThanMax" [
          ("block_blob_gas_price", φ block_blob_gas_price);
          ("tx_max_fee_per_blob_gas", φ tx_max_fee_per_blob_gas)
        ]
      | EmptyBlobs =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::EmptyBlobs" []
      | BlobCreateTransaction =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobCreateTransaction" []
      | TooManyBlobs max have =>
        Value.StructRecord "revm_context_interface::result::InvalidTransaction::TooManyBlobs" [
          ("max", φ max);
          ("have", φ have)
        ]
      | BlobVersionNotSupported =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobVersionNotSupported" []
      | AuthorizationListNotSupported =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::AuthorizationListNotSupported" []
      | AuthorizationListInvalidFields =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::AuthorizationListInvalidFields" []
      | EmptyAuthorizationList =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::EmptyAuthorizationList" []
      | Eip2930NotSupported =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip2930NotSupported" []
      | Eip1559NotSupported =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip1559NotSupported" []
      | Eip4844NotSupported =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip4844NotSupported" []
      | Eip7702NotSupported =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip7702NotSupported" []
      | Eip7873NotSupported =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip7873NotSupported" []
      | Eip7873MissingTarget =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip7873MissingTarget" []
      | Str γ0 =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::Str" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::result::InvalidTransaction").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_PriorityFeeGreaterThanMaxFee :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::PriorityFeeGreaterThanMaxFee" [] =
    φ PriorityFeeGreaterThanMaxFee.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PriorityFeeGreaterThanMaxFee : of_value.

  Lemma of_value_with_GasPriceLessThanBasefee :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::GasPriceLessThanBasefee" [] =
    φ GasPriceLessThanBasefee.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_GasPriceLessThanBasefee : of_value.

  Lemma of_value_with_CallerGasLimitMoreThanBlock :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::CallerGasLimitMoreThanBlock" [] =
    φ CallerGasLimitMoreThanBlock.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CallerGasLimitMoreThanBlock : of_value.

  Lemma of_value_with_CallGasCostMoreThanGasLimit
    (initial_gas : U64.t) (initial_gas' : Value.t)
    (gas_limit : U64.t) (gas_limit' : Value.t) :
    initial_gas' = φ initial_gas ->
    gas_limit' = φ gas_limit ->
    Value.StructRecord "revm_context_interface::result::InvalidTransaction::CallGasCostMoreThanGasLimit" [
      ("initial_gas", initial_gas');
      ("gas_limit", gas_limit')
    ] =
    φ (CallGasCostMoreThanGasLimit initial_gas gas_limit).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CallGasCostMoreThanGasLimit : of_value.

  Lemma of_value_with_GasFloorMoreThanGasLimit
    (gas_floor : U64.t) (gas_floor' : Value.t)
    (gas_limit : U64.t) (gas_limit' : Value.t) :
    gas_floor' = φ gas_floor ->
    gas_limit' = φ gas_limit ->
    Value.StructRecord "revm_context_interface::result::InvalidTransaction::GasFloorMoreThanGasLimit" [
      ("gas_floor", gas_floor');
      ("gas_limit", gas_limit')
    ] =
    φ (GasFloorMoreThanGasLimit gas_floor gas_limit).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_GasFloorMoreThanGasLimit : of_value.

  Lemma of_value_with_RejectCallerWithCode :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::RejectCallerWithCode" [] =
    φ RejectCallerWithCode.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_RejectCallerWithCode : of_value.

  Lemma of_value_with_LackOfFundForMaxFee
    (fee : boxed.Box.t (ruint.Uint.t 256 4) alloc.Global.t) (fee' : Value.t)
    (balance : boxed.Box.t (ruint.Uint.t 256 4) alloc.Global.t) (balance' : Value.t) :
    fee' = φ fee ->
    balance' = φ balance ->
    Value.StructRecord "revm_context_interface::result::InvalidTransaction::LackOfFundForMaxFee" [
      ("fee", fee');
      ("balance", balance')
    ] =
    φ (LackOfFundForMaxFee fee balance).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_LackOfFundForMaxFee : of_value.

  Lemma of_value_with_OverflowPaymentInTransaction :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::OverflowPaymentInTransaction" [] =
    φ OverflowPaymentInTransaction.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OverflowPaymentInTransaction : of_value.

  Lemma of_value_with_NonceOverflowInTransaction :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::NonceOverflowInTransaction" [] =
    φ NonceOverflowInTransaction.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NonceOverflowInTransaction : of_value.

  Lemma of_value_with_NonceTooHigh
    (tx : U64.t) (tx' : Value.t)
    (state : U64.t) (state' : Value.t) :
    tx' = φ tx ->
    state' = φ state ->
    Value.StructRecord "revm_context_interface::result::InvalidTransaction::NonceTooHigh" [
      ("tx", tx');
      ("state", state')
    ] =
    φ (NonceTooHigh tx state).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NonceTooHigh : of_value.

  Lemma of_value_with_NonceTooLow
    (tx : U64.t) (tx' : Value.t)
    (state : U64.t) (state' : Value.t) :
    tx' = φ tx ->
    state' = φ state ->
    Value.StructRecord "revm_context_interface::result::InvalidTransaction::NonceTooLow" [
      ("tx", tx');
      ("state", state')
    ] =
    φ (NonceTooLow tx state).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NonceTooLow : of_value.

  Lemma of_value_with_CreateInitCodeSizeLimit :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::CreateInitCodeSizeLimit" [] =
    φ CreateInitCodeSizeLimit.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateInitCodeSizeLimit : of_value.

  Lemma of_value_with_InvalidChainId :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::InvalidChainId" [] =
    φ InvalidChainId.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidChainId : of_value.

  Lemma of_value_with_MissingChainId :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::MissingChainId" [] =
    φ MissingChainId.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MissingChainId : of_value.

  Lemma of_value_with_TxGasLimitGreaterThanCap
    (gas_limit : U64.t) (gas_limit' : Value.t)
    (cap : U64.t) (cap' : Value.t) :
    gas_limit' = φ gas_limit ->
    cap' = φ cap ->
    Value.StructRecord "revm_context_interface::result::InvalidTransaction::TxGasLimitGreaterThanCap" [
      ("gas_limit", gas_limit');
      ("cap", cap')
    ] =
    φ (TxGasLimitGreaterThanCap gas_limit cap).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_TxGasLimitGreaterThanCap : of_value.

  Lemma of_value_with_AccessListNotSupported :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::AccessListNotSupported" [] =
    φ AccessListNotSupported.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_AccessListNotSupported : of_value.

  Lemma of_value_with_MaxFeePerBlobGasNotSupported :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::MaxFeePerBlobGasNotSupported" [] =
    φ MaxFeePerBlobGasNotSupported.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MaxFeePerBlobGasNotSupported : of_value.

  Lemma of_value_with_BlobVersionedHashesNotSupported :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobVersionedHashesNotSupported" [] =
    φ BlobVersionedHashesNotSupported.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BlobVersionedHashesNotSupported : of_value.

  Lemma of_value_with_BlobGasPriceGreaterThanMax
    (block_blob_gas_price : U128.t) (block_blob_gas_price' : Value.t)
    (tx_max_fee_per_blob_gas : U128.t) (tx_max_fee_per_blob_gas' : Value.t) :
    block_blob_gas_price' = φ block_blob_gas_price ->
    tx_max_fee_per_blob_gas' = φ tx_max_fee_per_blob_gas ->
    Value.StructRecord "revm_context_interface::result::InvalidTransaction::BlobGasPriceGreaterThanMax" [
      ("block_blob_gas_price", block_blob_gas_price');
      ("tx_max_fee_per_blob_gas", tx_max_fee_per_blob_gas')
    ] =
    φ (BlobGasPriceGreaterThanMax block_blob_gas_price tx_max_fee_per_blob_gas).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BlobGasPriceGreaterThanMax : of_value.

  Lemma of_value_with_EmptyBlobs :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::EmptyBlobs" [] =
    φ EmptyBlobs.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_EmptyBlobs : of_value.

  Lemma of_value_with_BlobCreateTransaction :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobCreateTransaction" [] =
    φ BlobCreateTransaction.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BlobCreateTransaction : of_value.

  Lemma of_value_with_TooManyBlobs
    (max : Usize.t) (max' : Value.t)
    (have : Usize.t) (have' : Value.t) :
    max' = φ max ->
    have' = φ have ->
    Value.StructRecord "revm_context_interface::result::InvalidTransaction::TooManyBlobs" [
      ("max", max');
      ("have", have')
    ] =
    φ (TooManyBlobs max have).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_TooManyBlobs : of_value.

  Lemma of_value_with_BlobVersionNotSupported :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobVersionNotSupported" [] =
    φ BlobVersionNotSupported.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BlobVersionNotSupported : of_value.

  Lemma of_value_with_AuthorizationListNotSupported :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::AuthorizationListNotSupported" [] =
    φ AuthorizationListNotSupported.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_AuthorizationListNotSupported : of_value.

  Lemma of_value_with_AuthorizationListInvalidFields :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::AuthorizationListInvalidFields" [] =
    φ AuthorizationListInvalidFields.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_AuthorizationListInvalidFields : of_value.

  Lemma of_value_with_EmptyAuthorizationList :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::EmptyAuthorizationList" [] =
    φ EmptyAuthorizationList.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_EmptyAuthorizationList : of_value.

  Lemma of_value_with_Eip2930NotSupported :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip2930NotSupported" [] =
    φ Eip2930NotSupported.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip2930NotSupported : of_value.

  Lemma of_value_with_Eip1559NotSupported :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip1559NotSupported" [] =
    φ Eip1559NotSupported.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip1559NotSupported : of_value.

  Lemma of_value_with_Eip4844NotSupported :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip4844NotSupported" [] =
    φ Eip4844NotSupported.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip4844NotSupported : of_value.

  Lemma of_value_with_Eip7702NotSupported :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip7702NotSupported" [] =
    φ Eip7702NotSupported.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip7702NotSupported : of_value.

  Lemma of_value_with_Eip7873NotSupported :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip7873NotSupported" [] =
    φ Eip7873NotSupported.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip7873NotSupported : of_value.

  Lemma of_value_with_Eip7873MissingTarget :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip7873MissingTarget" [] =
    φ Eip7873MissingTarget.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip7873MissingTarget : of_value.

  Lemma of_value_with_Str
    (γ0 : borrow.Cow.t str.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::Str" [
      γ0
    ] =
    φ (Str γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Str : of_value.

  Definition of_value_PriorityFeeGreaterThanMaxFee :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::PriorityFeeGreaterThanMaxFee" []
    ).
  Proof. econstructor; apply of_value_with_PriorityFeeGreaterThanMaxFee; eassumption. Defined.
  Smpl Add simple apply of_value_PriorityFeeGreaterThanMaxFee : of_value.

  Definition of_value_GasPriceLessThanBasefee :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::GasPriceLessThanBasefee" []
    ).
  Proof. econstructor; apply of_value_with_GasPriceLessThanBasefee; eassumption. Defined.
  Smpl Add simple apply of_value_GasPriceLessThanBasefee : of_value.

  Definition of_value_CallerGasLimitMoreThanBlock :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::CallerGasLimitMoreThanBlock" []
    ).
  Proof. econstructor; apply of_value_with_CallerGasLimitMoreThanBlock; eassumption. Defined.
  Smpl Add simple apply of_value_CallerGasLimitMoreThanBlock : of_value.

  Definition of_value_CallGasCostMoreThanGasLimit
    (initial_gas : U64.t) (initial_gas' : Value.t)
    (gas_limit : U64.t) (gas_limit' : Value.t) :
    initial_gas' = φ initial_gas ->
    gas_limit' = φ gas_limit ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::result::InvalidTransaction::CallGasCostMoreThanGasLimit" [
        ("initial_gas", initial_gas');
        ("gas_limit", gas_limit')
      ]
    ).
  Proof. econstructor; apply of_value_with_CallGasCostMoreThanGasLimit; eassumption. Defined.
  Smpl Add simple apply of_value_CallGasCostMoreThanGasLimit : of_value.

  Definition of_value_GasFloorMoreThanGasLimit
    (gas_floor : U64.t) (gas_floor' : Value.t)
    (gas_limit : U64.t) (gas_limit' : Value.t) :
    gas_floor' = φ gas_floor ->
    gas_limit' = φ gas_limit ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::result::InvalidTransaction::GasFloorMoreThanGasLimit" [
        ("gas_floor", gas_floor');
        ("gas_limit", gas_limit')
      ]
    ).
  Proof. econstructor; apply of_value_with_GasFloorMoreThanGasLimit; eassumption. Defined.
  Smpl Add simple apply of_value_GasFloorMoreThanGasLimit : of_value.

  Definition of_value_RejectCallerWithCode :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::RejectCallerWithCode" []
    ).
  Proof. econstructor; apply of_value_with_RejectCallerWithCode; eassumption. Defined.
  Smpl Add simple apply of_value_RejectCallerWithCode : of_value.

  Definition of_value_LackOfFundForMaxFee
    (fee : boxed.Box.t (ruint.Uint.t 256 4) alloc.Global.t) (fee' : Value.t)
    (balance : boxed.Box.t (ruint.Uint.t 256 4) alloc.Global.t) (balance' : Value.t) :
    fee' = φ fee ->
    balance' = φ balance ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::result::InvalidTransaction::LackOfFundForMaxFee" [
        ("fee", fee');
        ("balance", balance')
      ]
    ).
  Proof. econstructor; apply of_value_with_LackOfFundForMaxFee; eassumption. Defined.
  Smpl Add simple apply of_value_LackOfFundForMaxFee : of_value.

  Definition of_value_OverflowPaymentInTransaction :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::OverflowPaymentInTransaction" []
    ).
  Proof. econstructor; apply of_value_with_OverflowPaymentInTransaction; eassumption. Defined.
  Smpl Add simple apply of_value_OverflowPaymentInTransaction : of_value.

  Definition of_value_NonceOverflowInTransaction :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::NonceOverflowInTransaction" []
    ).
  Proof. econstructor; apply of_value_with_NonceOverflowInTransaction; eassumption. Defined.
  Smpl Add simple apply of_value_NonceOverflowInTransaction : of_value.

  Definition of_value_NonceTooHigh
    (tx : U64.t) (tx' : Value.t)
    (state : U64.t) (state' : Value.t) :
    tx' = φ tx ->
    state' = φ state ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::result::InvalidTransaction::NonceTooHigh" [
        ("tx", tx');
        ("state", state')
      ]
    ).
  Proof. econstructor; apply of_value_with_NonceTooHigh; eassumption. Defined.
  Smpl Add simple apply of_value_NonceTooHigh : of_value.

  Definition of_value_NonceTooLow
    (tx : U64.t) (tx' : Value.t)
    (state : U64.t) (state' : Value.t) :
    tx' = φ tx ->
    state' = φ state ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::result::InvalidTransaction::NonceTooLow" [
        ("tx", tx');
        ("state", state')
      ]
    ).
  Proof. econstructor; apply of_value_with_NonceTooLow; eassumption. Defined.
  Smpl Add simple apply of_value_NonceTooLow : of_value.

  Definition of_value_CreateInitCodeSizeLimit :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::CreateInitCodeSizeLimit" []
    ).
  Proof. econstructor; apply of_value_with_CreateInitCodeSizeLimit; eassumption. Defined.
  Smpl Add simple apply of_value_CreateInitCodeSizeLimit : of_value.

  Definition of_value_InvalidChainId :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::InvalidChainId" []
    ).
  Proof. econstructor; apply of_value_with_InvalidChainId; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidChainId : of_value.

  Definition of_value_MissingChainId :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::MissingChainId" []
    ).
  Proof. econstructor; apply of_value_with_MissingChainId; eassumption. Defined.
  Smpl Add simple apply of_value_MissingChainId : of_value.

  Definition of_value_TxGasLimitGreaterThanCap
    (gas_limit : U64.t) (gas_limit' : Value.t)
    (cap : U64.t) (cap' : Value.t) :
    gas_limit' = φ gas_limit ->
    cap' = φ cap ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::result::InvalidTransaction::TxGasLimitGreaterThanCap" [
        ("gas_limit", gas_limit');
        ("cap", cap')
      ]
    ).
  Proof. econstructor; apply of_value_with_TxGasLimitGreaterThanCap; eassumption. Defined.
  Smpl Add simple apply of_value_TxGasLimitGreaterThanCap : of_value.

  Definition of_value_AccessListNotSupported :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::AccessListNotSupported" []
    ).
  Proof. econstructor; apply of_value_with_AccessListNotSupported; eassumption. Defined.
  Smpl Add simple apply of_value_AccessListNotSupported : of_value.

  Definition of_value_MaxFeePerBlobGasNotSupported :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::MaxFeePerBlobGasNotSupported" []
    ).
  Proof. econstructor; apply of_value_with_MaxFeePerBlobGasNotSupported; eassumption. Defined.
  Smpl Add simple apply of_value_MaxFeePerBlobGasNotSupported : of_value.

  Definition of_value_BlobVersionedHashesNotSupported :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobVersionedHashesNotSupported" []
    ).
  Proof. econstructor; apply of_value_with_BlobVersionedHashesNotSupported; eassumption. Defined.
  Smpl Add simple apply of_value_BlobVersionedHashesNotSupported : of_value.

  Definition of_value_BlobGasPriceGreaterThanMax
    (block_blob_gas_price : U128.t) (block_blob_gas_price' : Value.t)
    (tx_max_fee_per_blob_gas : U128.t) (tx_max_fee_per_blob_gas' : Value.t) :
    block_blob_gas_price' = φ block_blob_gas_price ->
    tx_max_fee_per_blob_gas' = φ tx_max_fee_per_blob_gas ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::result::InvalidTransaction::BlobGasPriceGreaterThanMax" [
        ("block_blob_gas_price", block_blob_gas_price');
        ("tx_max_fee_per_blob_gas", tx_max_fee_per_blob_gas')
      ]
    ).
  Proof. econstructor; apply of_value_with_BlobGasPriceGreaterThanMax; eassumption. Defined.
  Smpl Add simple apply of_value_BlobGasPriceGreaterThanMax : of_value.

  Definition of_value_EmptyBlobs :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::EmptyBlobs" []
    ).
  Proof. econstructor; apply of_value_with_EmptyBlobs; eassumption. Defined.
  Smpl Add simple apply of_value_EmptyBlobs : of_value.

  Definition of_value_BlobCreateTransaction :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobCreateTransaction" []
    ).
  Proof. econstructor; apply of_value_with_BlobCreateTransaction; eassumption. Defined.
  Smpl Add simple apply of_value_BlobCreateTransaction : of_value.

  Definition of_value_TooManyBlobs
    (max : Usize.t) (max' : Value.t)
    (have : Usize.t) (have' : Value.t) :
    max' = φ max ->
    have' = φ have ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::result::InvalidTransaction::TooManyBlobs" [
        ("max", max');
        ("have", have')
      ]
    ).
  Proof. econstructor; apply of_value_with_TooManyBlobs; eassumption. Defined.
  Smpl Add simple apply of_value_TooManyBlobs : of_value.

  Definition of_value_BlobVersionNotSupported :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobVersionNotSupported" []
    ).
  Proof. econstructor; apply of_value_with_BlobVersionNotSupported; eassumption. Defined.
  Smpl Add simple apply of_value_BlobVersionNotSupported : of_value.

  Definition of_value_AuthorizationListNotSupported :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::AuthorizationListNotSupported" []
    ).
  Proof. econstructor; apply of_value_with_AuthorizationListNotSupported; eassumption. Defined.
  Smpl Add simple apply of_value_AuthorizationListNotSupported : of_value.

  Definition of_value_AuthorizationListInvalidFields :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::AuthorizationListInvalidFields" []
    ).
  Proof. econstructor; apply of_value_with_AuthorizationListInvalidFields; eassumption. Defined.
  Smpl Add simple apply of_value_AuthorizationListInvalidFields : of_value.

  Definition of_value_EmptyAuthorizationList :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::EmptyAuthorizationList" []
    ).
  Proof. econstructor; apply of_value_with_EmptyAuthorizationList; eassumption. Defined.
  Smpl Add simple apply of_value_EmptyAuthorizationList : of_value.

  Definition of_value_Eip2930NotSupported :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip2930NotSupported" []
    ).
  Proof. econstructor; apply of_value_with_Eip2930NotSupported; eassumption. Defined.
  Smpl Add simple apply of_value_Eip2930NotSupported : of_value.

  Definition of_value_Eip1559NotSupported :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip1559NotSupported" []
    ).
  Proof. econstructor; apply of_value_with_Eip1559NotSupported; eassumption. Defined.
  Smpl Add simple apply of_value_Eip1559NotSupported : of_value.

  Definition of_value_Eip4844NotSupported :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip4844NotSupported" []
    ).
  Proof. econstructor; apply of_value_with_Eip4844NotSupported; eassumption. Defined.
  Smpl Add simple apply of_value_Eip4844NotSupported : of_value.

  Definition of_value_Eip7702NotSupported :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip7702NotSupported" []
    ).
  Proof. econstructor; apply of_value_with_Eip7702NotSupported; eassumption. Defined.
  Smpl Add simple apply of_value_Eip7702NotSupported : of_value.

  Definition of_value_Eip7873NotSupported :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip7873NotSupported" []
    ).
  Proof. econstructor; apply of_value_with_Eip7873NotSupported; eassumption. Defined.
  Smpl Add simple apply of_value_Eip7873NotSupported : of_value.

  Definition of_value_Eip7873MissingTarget :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip7873MissingTarget" []
    ).
  Proof. econstructor; apply of_value_with_Eip7873MissingTarget; eassumption. Defined.
  Smpl Add simple apply of_value_Eip7873MissingTarget : of_value.

  Definition of_value_Str
    (γ0 : borrow.Cow.t str.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::Str" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Str; eassumption. Defined.
  Smpl Add simple apply of_value_Str : of_value.

  Module SubPointer.
    Definition get_CallGasCostMoreThanGasLimit_initial_gas : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::InvalidTransaction::CallGasCostMoreThanGasLimit" "initial_gas") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | CallGasCostMoreThanGasLimit γ_initial_gas _ => Some γ_initial_gas
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_initial_gas : U64.t) :=
        match γ with
        | CallGasCostMoreThanGasLimit _ γ_gas_limit => Some (CallGasCostMoreThanGasLimit γ_initial_gas γ_gas_limit)
        | _ => None
        end;
    |}.

    Lemma get_CallGasCostMoreThanGasLimit_initial_gas_is_valid : SubPointer.Runner.Valid.t get_CallGasCostMoreThanGasLimit_initial_gas.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_CallGasCostMoreThanGasLimit_initial_gas_is_valid : run_sub_pointer.

    Definition get_CallGasCostMoreThanGasLimit_gas_limit : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::InvalidTransaction::CallGasCostMoreThanGasLimit" "gas_limit") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | CallGasCostMoreThanGasLimit _ γ_gas_limit => Some γ_gas_limit
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_gas_limit : U64.t) :=
        match γ with
        | CallGasCostMoreThanGasLimit γ_initial_gas _ => Some (CallGasCostMoreThanGasLimit γ_initial_gas γ_gas_limit)
        | _ => None
        end;
    |}.

    Lemma get_CallGasCostMoreThanGasLimit_gas_limit_is_valid : SubPointer.Runner.Valid.t get_CallGasCostMoreThanGasLimit_gas_limit.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_CallGasCostMoreThanGasLimit_gas_limit_is_valid : run_sub_pointer.

    Definition get_GasFloorMoreThanGasLimit_gas_floor : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::InvalidTransaction::GasFloorMoreThanGasLimit" "gas_floor") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | GasFloorMoreThanGasLimit γ_gas_floor _ => Some γ_gas_floor
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_gas_floor : U64.t) :=
        match γ with
        | GasFloorMoreThanGasLimit _ γ_gas_limit => Some (GasFloorMoreThanGasLimit γ_gas_floor γ_gas_limit)
        | _ => None
        end;
    |}.

    Lemma get_GasFloorMoreThanGasLimit_gas_floor_is_valid : SubPointer.Runner.Valid.t get_GasFloorMoreThanGasLimit_gas_floor.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_GasFloorMoreThanGasLimit_gas_floor_is_valid : run_sub_pointer.

    Definition get_GasFloorMoreThanGasLimit_gas_limit : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::InvalidTransaction::GasFloorMoreThanGasLimit" "gas_limit") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | GasFloorMoreThanGasLimit _ γ_gas_limit => Some γ_gas_limit
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_gas_limit : U64.t) :=
        match γ with
        | GasFloorMoreThanGasLimit γ_gas_floor _ => Some (GasFloorMoreThanGasLimit γ_gas_floor γ_gas_limit)
        | _ => None
        end;
    |}.

    Lemma get_GasFloorMoreThanGasLimit_gas_limit_is_valid : SubPointer.Runner.Valid.t get_GasFloorMoreThanGasLimit_gas_limit.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_GasFloorMoreThanGasLimit_gas_limit_is_valid : run_sub_pointer.

    Definition get_LackOfFundForMaxFee_fee : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::InvalidTransaction::LackOfFundForMaxFee" "fee") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | LackOfFundForMaxFee γ_fee _ => Some γ_fee
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_fee : boxed.Box.t (ruint.Uint.t 256 4) alloc.Global.t) :=
        match γ with
        | LackOfFundForMaxFee _ γ_balance => Some (LackOfFundForMaxFee γ_fee γ_balance)
        | _ => None
        end;
    |}.

    Lemma get_LackOfFundForMaxFee_fee_is_valid : SubPointer.Runner.Valid.t get_LackOfFundForMaxFee_fee.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_LackOfFundForMaxFee_fee_is_valid : run_sub_pointer.

    Definition get_LackOfFundForMaxFee_balance : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::InvalidTransaction::LackOfFundForMaxFee" "balance") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | LackOfFundForMaxFee _ γ_balance => Some γ_balance
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_balance : boxed.Box.t (ruint.Uint.t 256 4) alloc.Global.t) :=
        match γ with
        | LackOfFundForMaxFee γ_fee _ => Some (LackOfFundForMaxFee γ_fee γ_balance)
        | _ => None
        end;
    |}.

    Lemma get_LackOfFundForMaxFee_balance_is_valid : SubPointer.Runner.Valid.t get_LackOfFundForMaxFee_balance.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_LackOfFundForMaxFee_balance_is_valid : run_sub_pointer.

    Definition get_NonceTooHigh_tx : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::InvalidTransaction::NonceTooHigh" "tx") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | NonceTooHigh γ_tx _ => Some γ_tx
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_tx : U64.t) :=
        match γ with
        | NonceTooHigh _ γ_state => Some (NonceTooHigh γ_tx γ_state)
        | _ => None
        end;
    |}.

    Lemma get_NonceTooHigh_tx_is_valid : SubPointer.Runner.Valid.t get_NonceTooHigh_tx.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_NonceTooHigh_tx_is_valid : run_sub_pointer.

    Definition get_NonceTooHigh_state : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::InvalidTransaction::NonceTooHigh" "state") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | NonceTooHigh _ γ_state => Some γ_state
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_state : U64.t) :=
        match γ with
        | NonceTooHigh γ_tx _ => Some (NonceTooHigh γ_tx γ_state)
        | _ => None
        end;
    |}.

    Lemma get_NonceTooHigh_state_is_valid : SubPointer.Runner.Valid.t get_NonceTooHigh_state.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_NonceTooHigh_state_is_valid : run_sub_pointer.

    Definition get_NonceTooLow_tx : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::InvalidTransaction::NonceTooLow" "tx") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | NonceTooLow γ_tx _ => Some γ_tx
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_tx : U64.t) :=
        match γ with
        | NonceTooLow _ γ_state => Some (NonceTooLow γ_tx γ_state)
        | _ => None
        end;
    |}.

    Lemma get_NonceTooLow_tx_is_valid : SubPointer.Runner.Valid.t get_NonceTooLow_tx.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_NonceTooLow_tx_is_valid : run_sub_pointer.

    Definition get_NonceTooLow_state : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::InvalidTransaction::NonceTooLow" "state") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | NonceTooLow _ γ_state => Some γ_state
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_state : U64.t) :=
        match γ with
        | NonceTooLow γ_tx _ => Some (NonceTooLow γ_tx γ_state)
        | _ => None
        end;
    |}.

    Lemma get_NonceTooLow_state_is_valid : SubPointer.Runner.Valid.t get_NonceTooLow_state.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_NonceTooLow_state_is_valid : run_sub_pointer.

    Definition get_TxGasLimitGreaterThanCap_gas_limit : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::InvalidTransaction::TxGasLimitGreaterThanCap" "gas_limit") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | TxGasLimitGreaterThanCap γ_gas_limit _ => Some γ_gas_limit
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_gas_limit : U64.t) :=
        match γ with
        | TxGasLimitGreaterThanCap _ γ_cap => Some (TxGasLimitGreaterThanCap γ_gas_limit γ_cap)
        | _ => None
        end;
    |}.

    Lemma get_TxGasLimitGreaterThanCap_gas_limit_is_valid : SubPointer.Runner.Valid.t get_TxGasLimitGreaterThanCap_gas_limit.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_TxGasLimitGreaterThanCap_gas_limit_is_valid : run_sub_pointer.

    Definition get_TxGasLimitGreaterThanCap_cap : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::InvalidTransaction::TxGasLimitGreaterThanCap" "cap") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | TxGasLimitGreaterThanCap _ γ_cap => Some γ_cap
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_cap : U64.t) :=
        match γ with
        | TxGasLimitGreaterThanCap γ_gas_limit _ => Some (TxGasLimitGreaterThanCap γ_gas_limit γ_cap)
        | _ => None
        end;
    |}.

    Lemma get_TxGasLimitGreaterThanCap_cap_is_valid : SubPointer.Runner.Valid.t get_TxGasLimitGreaterThanCap_cap.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_TxGasLimitGreaterThanCap_cap_is_valid : run_sub_pointer.

    Definition get_BlobGasPriceGreaterThanMax_block_blob_gas_price : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::InvalidTransaction::BlobGasPriceGreaterThanMax" "block_blob_gas_price") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | BlobGasPriceGreaterThanMax γ_block_blob_gas_price _ => Some γ_block_blob_gas_price
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_block_blob_gas_price : U128.t) :=
        match γ with
        | BlobGasPriceGreaterThanMax _ γ_tx_max_fee_per_blob_gas => Some (BlobGasPriceGreaterThanMax γ_block_blob_gas_price γ_tx_max_fee_per_blob_gas)
        | _ => None
        end;
    |}.

    Lemma get_BlobGasPriceGreaterThanMax_block_blob_gas_price_is_valid : SubPointer.Runner.Valid.t get_BlobGasPriceGreaterThanMax_block_blob_gas_price.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_BlobGasPriceGreaterThanMax_block_blob_gas_price_is_valid : run_sub_pointer.

    Definition get_BlobGasPriceGreaterThanMax_tx_max_fee_per_blob_gas : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::InvalidTransaction::BlobGasPriceGreaterThanMax" "tx_max_fee_per_blob_gas") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | BlobGasPriceGreaterThanMax _ γ_tx_max_fee_per_blob_gas => Some γ_tx_max_fee_per_blob_gas
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_tx_max_fee_per_blob_gas : U128.t) :=
        match γ with
        | BlobGasPriceGreaterThanMax γ_block_blob_gas_price _ => Some (BlobGasPriceGreaterThanMax γ_block_blob_gas_price γ_tx_max_fee_per_blob_gas)
        | _ => None
        end;
    |}.

    Lemma get_BlobGasPriceGreaterThanMax_tx_max_fee_per_blob_gas_is_valid : SubPointer.Runner.Valid.t get_BlobGasPriceGreaterThanMax_tx_max_fee_per_blob_gas.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_BlobGasPriceGreaterThanMax_tx_max_fee_per_blob_gas_is_valid : run_sub_pointer.

    Definition get_TooManyBlobs_max : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::InvalidTransaction::TooManyBlobs" "max") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | TooManyBlobs γ_max _ => Some γ_max
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_max : Usize.t) :=
        match γ with
        | TooManyBlobs _ γ_have => Some (TooManyBlobs γ_max γ_have)
        | _ => None
        end;
    |}.

    Lemma get_TooManyBlobs_max_is_valid : SubPointer.Runner.Valid.t get_TooManyBlobs_max.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_TooManyBlobs_max_is_valid : run_sub_pointer.

    Definition get_TooManyBlobs_have : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::result::InvalidTransaction::TooManyBlobs" "have") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | TooManyBlobs _ γ_have => Some γ_have
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_have : Usize.t) :=
        match γ with
        | TooManyBlobs γ_max _ => Some (TooManyBlobs γ_max γ_have)
        | _ => None
        end;
    |}.

    Lemma get_TooManyBlobs_have_is_valid : SubPointer.Runner.Valid.t get_TooManyBlobs_have.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_TooManyBlobs_have_is_valid : run_sub_pointer.

    Definition get_Str_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_context_interface::result::InvalidTransaction::Str" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Str γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : borrow.Cow.t str.t) :=
        match γ with
        | Str _ => Some (Str γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Str_0_is_valid : SubPointer.Runner.Valid.t get_Str_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Str_0_is_valid : run_sub_pointer.
  End SubPointer.
End InvalidTransaction.

Module InvalidHeader.
  Inductive t : Set :=
  | PrevrandaoNotSet
  | ExcessBlobGasNotSet
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::result::InvalidHeader";
    φ x :=
      match x with
      | PrevrandaoNotSet =>
        Value.StructTuple "revm_context_interface::result::InvalidHeader::PrevrandaoNotSet" []
      | ExcessBlobGasNotSet =>
        Value.StructTuple "revm_context_interface::result::InvalidHeader::ExcessBlobGasNotSet" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::result::InvalidHeader").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_PrevrandaoNotSet :
    Value.StructTuple "revm_context_interface::result::InvalidHeader::PrevrandaoNotSet" [] =
    φ PrevrandaoNotSet.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PrevrandaoNotSet : of_value.

  Lemma of_value_with_ExcessBlobGasNotSet :
    Value.StructTuple "revm_context_interface::result::InvalidHeader::ExcessBlobGasNotSet" [] =
    φ ExcessBlobGasNotSet.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ExcessBlobGasNotSet : of_value.

  Definition of_value_PrevrandaoNotSet :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidHeader::PrevrandaoNotSet" []
    ).
  Proof. econstructor; apply of_value_with_PrevrandaoNotSet; eassumption. Defined.
  Smpl Add simple apply of_value_PrevrandaoNotSet : of_value.

  Definition of_value_ExcessBlobGasNotSet :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidHeader::ExcessBlobGasNotSet" []
    ).
  Proof. econstructor; apply of_value_with_ExcessBlobGasNotSet; eassumption. Defined.
  Smpl Add simple apply of_value_ExcessBlobGasNotSet : of_value.

  Module SubPointer.

  End SubPointer.
End InvalidHeader.

Module SuccessReason.
  Inductive t : Set :=
  | Stop
  | Return
  | SelfDestruct
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::result::SuccessReason";
    φ x :=
      match x with
      | Stop =>
        Value.StructTuple "revm_context_interface::result::SuccessReason::Stop" []
      | Return =>
        Value.StructTuple "revm_context_interface::result::SuccessReason::Return" []
      | SelfDestruct =>
        Value.StructTuple "revm_context_interface::result::SuccessReason::SelfDestruct" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::result::SuccessReason").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Stop :
    Value.StructTuple "revm_context_interface::result::SuccessReason::Stop" [] =
    φ Stop.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Stop : of_value.

  Lemma of_value_with_Return :
    Value.StructTuple "revm_context_interface::result::SuccessReason::Return" [] =
    φ Return.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Return : of_value.

  Lemma of_value_with_SelfDestruct :
    Value.StructTuple "revm_context_interface::result::SuccessReason::SelfDestruct" [] =
    φ SelfDestruct.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_SelfDestruct : of_value.

  Definition of_value_Stop :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::SuccessReason::Stop" []
    ).
  Proof. econstructor; apply of_value_with_Stop; eassumption. Defined.
  Smpl Add simple apply of_value_Stop : of_value.

  Definition of_value_Return :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::SuccessReason::Return" []
    ).
  Proof. econstructor; apply of_value_with_Return; eassumption. Defined.
  Smpl Add simple apply of_value_Return : of_value.

  Definition of_value_SelfDestruct :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::SuccessReason::SelfDestruct" []
    ).
  Proof. econstructor; apply of_value_with_SelfDestruct; eassumption. Defined.
  Smpl Add simple apply of_value_SelfDestruct : of_value.

  Module SubPointer.

  End SubPointer.
End SuccessReason.

Module HaltReason.
  Inductive t : Set :=
  | OutOfGas
    (_ : result.OutOfGasError.t)
  | OpcodeNotFound
  | InvalidFEOpcode
  | InvalidJump
  | NotActivated
  | StackUnderflow
  | StackOverflow
  | OutOfOffset
  | CreateCollision
  | PrecompileError
  | PrecompileErrorWithContext
    (_ : string.String.t)
  | NonceOverflow
  | CreateContractSizeLimit
  | CreateContractStartingWithEF
  | CreateInitCodeSizeLimit
  | OverflowPayment
  | StateChangeDuringStaticCall
  | CallNotAllowedInsideStatic
  | OutOfFunds
  | CallTooDeep
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::result::HaltReason";
    φ x :=
      match x with
      | OutOfGas γ0 =>
        Value.StructTuple "revm_context_interface::result::HaltReason::OutOfGas" [
          φ γ0
        ]
      | OpcodeNotFound =>
        Value.StructTuple "revm_context_interface::result::HaltReason::OpcodeNotFound" []
      | InvalidFEOpcode =>
        Value.StructTuple "revm_context_interface::result::HaltReason::InvalidFEOpcode" []
      | InvalidJump =>
        Value.StructTuple "revm_context_interface::result::HaltReason::InvalidJump" []
      | NotActivated =>
        Value.StructTuple "revm_context_interface::result::HaltReason::NotActivated" []
      | StackUnderflow =>
        Value.StructTuple "revm_context_interface::result::HaltReason::StackUnderflow" []
      | StackOverflow =>
        Value.StructTuple "revm_context_interface::result::HaltReason::StackOverflow" []
      | OutOfOffset =>
        Value.StructTuple "revm_context_interface::result::HaltReason::OutOfOffset" []
      | CreateCollision =>
        Value.StructTuple "revm_context_interface::result::HaltReason::CreateCollision" []
      | PrecompileError =>
        Value.StructTuple "revm_context_interface::result::HaltReason::PrecompileError" []
      | PrecompileErrorWithContext γ0 =>
        Value.StructTuple "revm_context_interface::result::HaltReason::PrecompileErrorWithContext" [
          φ γ0
        ]
      | NonceOverflow =>
        Value.StructTuple "revm_context_interface::result::HaltReason::NonceOverflow" []
      | CreateContractSizeLimit =>
        Value.StructTuple "revm_context_interface::result::HaltReason::CreateContractSizeLimit" []
      | CreateContractStartingWithEF =>
        Value.StructTuple "revm_context_interface::result::HaltReason::CreateContractStartingWithEF" []
      | CreateInitCodeSizeLimit =>
        Value.StructTuple "revm_context_interface::result::HaltReason::CreateInitCodeSizeLimit" []
      | OverflowPayment =>
        Value.StructTuple "revm_context_interface::result::HaltReason::OverflowPayment" []
      | StateChangeDuringStaticCall =>
        Value.StructTuple "revm_context_interface::result::HaltReason::StateChangeDuringStaticCall" []
      | CallNotAllowedInsideStatic =>
        Value.StructTuple "revm_context_interface::result::HaltReason::CallNotAllowedInsideStatic" []
      | OutOfFunds =>
        Value.StructTuple "revm_context_interface::result::HaltReason::OutOfFunds" []
      | CallTooDeep =>
        Value.StructTuple "revm_context_interface::result::HaltReason::CallTooDeep" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::result::HaltReason").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_OutOfGas
    (γ0 : result.OutOfGasError.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_context_interface::result::HaltReason::OutOfGas" [
      γ0
    ] =
    φ (OutOfGas γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfGas : of_value.

  Lemma of_value_with_OpcodeNotFound :
    Value.StructTuple "revm_context_interface::result::HaltReason::OpcodeNotFound" [] =
    φ OpcodeNotFound.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OpcodeNotFound : of_value.

  Lemma of_value_with_InvalidFEOpcode :
    Value.StructTuple "revm_context_interface::result::HaltReason::InvalidFEOpcode" [] =
    φ InvalidFEOpcode.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidFEOpcode : of_value.

  Lemma of_value_with_InvalidJump :
    Value.StructTuple "revm_context_interface::result::HaltReason::InvalidJump" [] =
    φ InvalidJump.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidJump : of_value.

  Lemma of_value_with_NotActivated :
    Value.StructTuple "revm_context_interface::result::HaltReason::NotActivated" [] =
    φ NotActivated.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NotActivated : of_value.

  Lemma of_value_with_StackUnderflow :
    Value.StructTuple "revm_context_interface::result::HaltReason::StackUnderflow" [] =
    φ StackUnderflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StackUnderflow : of_value.

  Lemma of_value_with_StackOverflow :
    Value.StructTuple "revm_context_interface::result::HaltReason::StackOverflow" [] =
    φ StackOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StackOverflow : of_value.

  Lemma of_value_with_OutOfOffset :
    Value.StructTuple "revm_context_interface::result::HaltReason::OutOfOffset" [] =
    φ OutOfOffset.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfOffset : of_value.

  Lemma of_value_with_CreateCollision :
    Value.StructTuple "revm_context_interface::result::HaltReason::CreateCollision" [] =
    φ CreateCollision.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateCollision : of_value.

  Lemma of_value_with_PrecompileError :
    Value.StructTuple "revm_context_interface::result::HaltReason::PrecompileError" [] =
    φ PrecompileError.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PrecompileError : of_value.

  Lemma of_value_with_PrecompileErrorWithContext
    (γ0 : string.String.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_context_interface::result::HaltReason::PrecompileErrorWithContext" [
      γ0
    ] =
    φ (PrecompileErrorWithContext γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PrecompileErrorWithContext : of_value.

  Lemma of_value_with_NonceOverflow :
    Value.StructTuple "revm_context_interface::result::HaltReason::NonceOverflow" [] =
    φ NonceOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NonceOverflow : of_value.

  Lemma of_value_with_CreateContractSizeLimit :
    Value.StructTuple "revm_context_interface::result::HaltReason::CreateContractSizeLimit" [] =
    φ CreateContractSizeLimit.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateContractSizeLimit : of_value.

  Lemma of_value_with_CreateContractStartingWithEF :
    Value.StructTuple "revm_context_interface::result::HaltReason::CreateContractStartingWithEF" [] =
    φ CreateContractStartingWithEF.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateContractStartingWithEF : of_value.

  Lemma of_value_with_CreateInitCodeSizeLimit :
    Value.StructTuple "revm_context_interface::result::HaltReason::CreateInitCodeSizeLimit" [] =
    φ CreateInitCodeSizeLimit.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateInitCodeSizeLimit : of_value.

  Lemma of_value_with_OverflowPayment :
    Value.StructTuple "revm_context_interface::result::HaltReason::OverflowPayment" [] =
    φ OverflowPayment.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OverflowPayment : of_value.

  Lemma of_value_with_StateChangeDuringStaticCall :
    Value.StructTuple "revm_context_interface::result::HaltReason::StateChangeDuringStaticCall" [] =
    φ StateChangeDuringStaticCall.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StateChangeDuringStaticCall : of_value.

  Lemma of_value_with_CallNotAllowedInsideStatic :
    Value.StructTuple "revm_context_interface::result::HaltReason::CallNotAllowedInsideStatic" [] =
    φ CallNotAllowedInsideStatic.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CallNotAllowedInsideStatic : of_value.

  Lemma of_value_with_OutOfFunds :
    Value.StructTuple "revm_context_interface::result::HaltReason::OutOfFunds" [] =
    φ OutOfFunds.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfFunds : of_value.

  Lemma of_value_with_CallTooDeep :
    Value.StructTuple "revm_context_interface::result::HaltReason::CallTooDeep" [] =
    φ CallTooDeep.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CallTooDeep : of_value.

  Definition of_value_OutOfGas
    (γ0 : result.OutOfGasError.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::OutOfGas" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_OutOfGas; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfGas : of_value.

  Definition of_value_OpcodeNotFound :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::OpcodeNotFound" []
    ).
  Proof. econstructor; apply of_value_with_OpcodeNotFound; eassumption. Defined.
  Smpl Add simple apply of_value_OpcodeNotFound : of_value.

  Definition of_value_InvalidFEOpcode :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::InvalidFEOpcode" []
    ).
  Proof. econstructor; apply of_value_with_InvalidFEOpcode; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidFEOpcode : of_value.

  Definition of_value_InvalidJump :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::InvalidJump" []
    ).
  Proof. econstructor; apply of_value_with_InvalidJump; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidJump : of_value.

  Definition of_value_NotActivated :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::NotActivated" []
    ).
  Proof. econstructor; apply of_value_with_NotActivated; eassumption. Defined.
  Smpl Add simple apply of_value_NotActivated : of_value.

  Definition of_value_StackUnderflow :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::StackUnderflow" []
    ).
  Proof. econstructor; apply of_value_with_StackUnderflow; eassumption. Defined.
  Smpl Add simple apply of_value_StackUnderflow : of_value.

  Definition of_value_StackOverflow :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::StackOverflow" []
    ).
  Proof. econstructor; apply of_value_with_StackOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_StackOverflow : of_value.

  Definition of_value_OutOfOffset :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::OutOfOffset" []
    ).
  Proof. econstructor; apply of_value_with_OutOfOffset; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfOffset : of_value.

  Definition of_value_CreateCollision :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::CreateCollision" []
    ).
  Proof. econstructor; apply of_value_with_CreateCollision; eassumption. Defined.
  Smpl Add simple apply of_value_CreateCollision : of_value.

  Definition of_value_PrecompileError :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::PrecompileError" []
    ).
  Proof. econstructor; apply of_value_with_PrecompileError; eassumption. Defined.
  Smpl Add simple apply of_value_PrecompileError : of_value.

  Definition of_value_PrecompileErrorWithContext
    (γ0 : string.String.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::PrecompileErrorWithContext" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_PrecompileErrorWithContext; eassumption. Defined.
  Smpl Add simple apply of_value_PrecompileErrorWithContext : of_value.

  Definition of_value_NonceOverflow :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::NonceOverflow" []
    ).
  Proof. econstructor; apply of_value_with_NonceOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_NonceOverflow : of_value.

  Definition of_value_CreateContractSizeLimit :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::CreateContractSizeLimit" []
    ).
  Proof. econstructor; apply of_value_with_CreateContractSizeLimit; eassumption. Defined.
  Smpl Add simple apply of_value_CreateContractSizeLimit : of_value.

  Definition of_value_CreateContractStartingWithEF :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::CreateContractStartingWithEF" []
    ).
  Proof. econstructor; apply of_value_with_CreateContractStartingWithEF; eassumption. Defined.
  Smpl Add simple apply of_value_CreateContractStartingWithEF : of_value.

  Definition of_value_CreateInitCodeSizeLimit :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::CreateInitCodeSizeLimit" []
    ).
  Proof. econstructor; apply of_value_with_CreateInitCodeSizeLimit; eassumption. Defined.
  Smpl Add simple apply of_value_CreateInitCodeSizeLimit : of_value.

  Definition of_value_OverflowPayment :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::OverflowPayment" []
    ).
  Proof. econstructor; apply of_value_with_OverflowPayment; eassumption. Defined.
  Smpl Add simple apply of_value_OverflowPayment : of_value.

  Definition of_value_StateChangeDuringStaticCall :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::StateChangeDuringStaticCall" []
    ).
  Proof. econstructor; apply of_value_with_StateChangeDuringStaticCall; eassumption. Defined.
  Smpl Add simple apply of_value_StateChangeDuringStaticCall : of_value.

  Definition of_value_CallNotAllowedInsideStatic :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::CallNotAllowedInsideStatic" []
    ).
  Proof. econstructor; apply of_value_with_CallNotAllowedInsideStatic; eassumption. Defined.
  Smpl Add simple apply of_value_CallNotAllowedInsideStatic : of_value.

  Definition of_value_OutOfFunds :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::OutOfFunds" []
    ).
  Proof. econstructor; apply of_value_with_OutOfFunds; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfFunds : of_value.

  Definition of_value_CallTooDeep :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::CallTooDeep" []
    ).
  Proof. econstructor; apply of_value_with_CallTooDeep; eassumption. Defined.
  Smpl Add simple apply of_value_CallTooDeep : of_value.

  Module SubPointer.
    Definition get_OutOfGas_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_context_interface::result::HaltReason::OutOfGas" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | OutOfGas γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : result.OutOfGasError.t) :=
        match γ with
        | OutOfGas _ => Some (OutOfGas γ_0)
        | _ => None
        end;
    |}.

    Lemma get_OutOfGas_0_is_valid : SubPointer.Runner.Valid.t get_OutOfGas_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_OutOfGas_0_is_valid : run_sub_pointer.

    Definition get_PrecompileErrorWithContext_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_context_interface::result::HaltReason::PrecompileErrorWithContext" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | PrecompileErrorWithContext γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : string.String.t) :=
        match γ with
        | PrecompileErrorWithContext _ => Some (PrecompileErrorWithContext γ_0)
        | _ => None
        end;
    |}.

    Lemma get_PrecompileErrorWithContext_0_is_valid : SubPointer.Runner.Valid.t get_PrecompileErrorWithContext_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_PrecompileErrorWithContext_0_is_valid : run_sub_pointer.
  End SubPointer.
End HaltReason.

Module OutOfGasError.
  Inductive t : Set :=
  | Basic
  | MemoryLimit
  | Memory
  | Precompile
  | InvalidOperand
  | ReentrancySentry
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::result::OutOfGasError";
    φ x :=
      match x with
      | Basic =>
        Value.StructTuple "revm_context_interface::result::OutOfGasError::Basic" []
      | MemoryLimit =>
        Value.StructTuple "revm_context_interface::result::OutOfGasError::MemoryLimit" []
      | Memory =>
        Value.StructTuple "revm_context_interface::result::OutOfGasError::Memory" []
      | Precompile =>
        Value.StructTuple "revm_context_interface::result::OutOfGasError::Precompile" []
      | InvalidOperand =>
        Value.StructTuple "revm_context_interface::result::OutOfGasError::InvalidOperand" []
      | ReentrancySentry =>
        Value.StructTuple "revm_context_interface::result::OutOfGasError::ReentrancySentry" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::result::OutOfGasError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Basic :
    Value.StructTuple "revm_context_interface::result::OutOfGasError::Basic" [] =
    φ Basic.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Basic : of_value.

  Lemma of_value_with_MemoryLimit :
    Value.StructTuple "revm_context_interface::result::OutOfGasError::MemoryLimit" [] =
    φ MemoryLimit.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MemoryLimit : of_value.

  Lemma of_value_with_Memory :
    Value.StructTuple "revm_context_interface::result::OutOfGasError::Memory" [] =
    φ Memory.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Memory : of_value.

  Lemma of_value_with_Precompile :
    Value.StructTuple "revm_context_interface::result::OutOfGasError::Precompile" [] =
    φ Precompile.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Precompile : of_value.

  Lemma of_value_with_InvalidOperand :
    Value.StructTuple "revm_context_interface::result::OutOfGasError::InvalidOperand" [] =
    φ InvalidOperand.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidOperand : of_value.

  Lemma of_value_with_ReentrancySentry :
    Value.StructTuple "revm_context_interface::result::OutOfGasError::ReentrancySentry" [] =
    φ ReentrancySentry.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ReentrancySentry : of_value.

  Definition of_value_Basic :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::OutOfGasError::Basic" []
    ).
  Proof. econstructor; apply of_value_with_Basic; eassumption. Defined.
  Smpl Add simple apply of_value_Basic : of_value.

  Definition of_value_MemoryLimit :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::OutOfGasError::MemoryLimit" []
    ).
  Proof. econstructor; apply of_value_with_MemoryLimit; eassumption. Defined.
  Smpl Add simple apply of_value_MemoryLimit : of_value.

  Definition of_value_Memory :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::OutOfGasError::Memory" []
    ).
  Proof. econstructor; apply of_value_with_Memory; eassumption. Defined.
  Smpl Add simple apply of_value_Memory : of_value.

  Definition of_value_Precompile :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::OutOfGasError::Precompile" []
    ).
  Proof. econstructor; apply of_value_with_Precompile; eassumption. Defined.
  Smpl Add simple apply of_value_Precompile : of_value.

  Definition of_value_InvalidOperand :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::OutOfGasError::InvalidOperand" []
    ).
  Proof. econstructor; apply of_value_with_InvalidOperand; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidOperand : of_value.

  Definition of_value_ReentrancySentry :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::OutOfGasError::ReentrancySentry" []
    ).
  Proof. econstructor; apply of_value_with_ReentrancySentry; eassumption. Defined.
  Smpl Add simple apply of_value_ReentrancySentry : of_value.

  Module SubPointer.

  End SubPointer.
End OutOfGasError.

Module TransactionIndexedError.
  Record t {Error: Set} : Set := {
    error: Error;
    transaction_index: Usize.t;
  }.
  Arguments Build_t {_}.
  Arguments t : clear implicits.

  Global Instance IsLink {Error: Set} `{Link Error} : Link (t Error) := {
    Φ := Ty.path "revm_context_interface::result::TransactionIndexedError";
    φ '(Build_t error transaction_index) :=
      Value.StructRecord "revm_context_interface::result::TransactionIndexedError" [
        ("error", φ error);
        ("transaction_index", φ transaction_index)
      ]
  }.
End TransactionIndexedError.

Module BlobExcessGasAndPrice.
  Record t : Set := {
    excess_blob_gas: U64.t;
    blob_gasprice: U128.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::block::blob::BlobExcessGasAndPrice";
    φ '(Build_t excess_blob_gas blob_gasprice) :=
      Value.StructRecord "revm_context_interface::block::blob::BlobExcessGasAndPrice" [
        ("excess_blob_gas", φ excess_blob_gas);
        ("blob_gasprice", φ blob_gasprice)
      ]
  }.
End BlobExcessGasAndPrice.

Module JournaledAccount.
  Record t {ENTRY: Set} : Set := {
    address: address.Address.t;
    account: '&mut revm_state.Account.t;
    journal_entries: '&mut (vec.Vec.t ENTRY alloc.Global.t);
  }.
  Arguments Build_t {_}.
  Arguments t : clear implicits.

  Global Instance IsLink {ENTRY: Set} `{Link ENTRY} : Link (t ENTRY) := {
    Φ := Ty.path "revm_context_interface::journaled_state::account::JournaledAccount";
    φ '(Build_t address account journal_entries) :=
      Value.StructRecord "revm_context_interface::journaled_state::account::JournaledAccount" [
        ("address", φ address);
        ("account", φ account);
        ("journal_entries", φ journal_entries)
      ]
  }.
End JournaledAccount.

Module SelfdestructionRevertStatus.
  Inductive t : Set :=
  | GloballySelfdestroyed
  | LocallySelfdestroyed
  | RepeatedSelfdestruction
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::journaled_state::entry::SelfdestructionRevertStatus";
    φ x :=
      match x with
      | GloballySelfdestroyed =>
        Value.StructTuple "revm_context_interface::journaled_state::entry::SelfdestructionRevertStatus::GloballySelfdestroyed" []
      | LocallySelfdestroyed =>
        Value.StructTuple "revm_context_interface::journaled_state::entry::SelfdestructionRevertStatus::LocallySelfdestroyed" []
      | RepeatedSelfdestruction =>
        Value.StructTuple "revm_context_interface::journaled_state::entry::SelfdestructionRevertStatus::RepeatedSelfdestruction" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::journaled_state::entry::SelfdestructionRevertStatus").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_GloballySelfdestroyed :
    Value.StructTuple "revm_context_interface::journaled_state::entry::SelfdestructionRevertStatus::GloballySelfdestroyed" [] =
    φ GloballySelfdestroyed.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_GloballySelfdestroyed : of_value.

  Lemma of_value_with_LocallySelfdestroyed :
    Value.StructTuple "revm_context_interface::journaled_state::entry::SelfdestructionRevertStatus::LocallySelfdestroyed" [] =
    φ LocallySelfdestroyed.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_LocallySelfdestroyed : of_value.

  Lemma of_value_with_RepeatedSelfdestruction :
    Value.StructTuple "revm_context_interface::journaled_state::entry::SelfdestructionRevertStatus::RepeatedSelfdestruction" [] =
    φ RepeatedSelfdestruction.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_RepeatedSelfdestruction : of_value.

  Definition of_value_GloballySelfdestroyed :
    OfValue.t (
      Value.StructTuple "revm_context_interface::journaled_state::entry::SelfdestructionRevertStatus::GloballySelfdestroyed" []
    ).
  Proof. econstructor; apply of_value_with_GloballySelfdestroyed; eassumption. Defined.
  Smpl Add simple apply of_value_GloballySelfdestroyed : of_value.

  Definition of_value_LocallySelfdestroyed :
    OfValue.t (
      Value.StructTuple "revm_context_interface::journaled_state::entry::SelfdestructionRevertStatus::LocallySelfdestroyed" []
    ).
  Proof. econstructor; apply of_value_with_LocallySelfdestroyed; eassumption. Defined.
  Smpl Add simple apply of_value_LocallySelfdestroyed : of_value.

  Definition of_value_RepeatedSelfdestruction :
    OfValue.t (
      Value.StructTuple "revm_context_interface::journaled_state::entry::SelfdestructionRevertStatus::RepeatedSelfdestruction" []
    ).
  Proof. econstructor; apply of_value_with_RepeatedSelfdestruction; eassumption. Defined.
  Smpl Add simple apply of_value_RepeatedSelfdestruction : of_value.

  Module SubPointer.

  End SubPointer.
End SelfdestructionRevertStatus.

Module JournalEntry.
  Inductive t : Set :=
  | AccountWarmed
    (address : address.Address.t)
  | AccountDestroyed
    (had_balance : ruint.Uint.t 256 4)
    (address : address.Address.t)
    (target : address.Address.t)
    (destroyed_status : entry.SelfdestructionRevertStatus.t)
  | AccountTouched
    (address : address.Address.t)
  | BalanceChange
    (old_balance : ruint.Uint.t 256 4)
    (address : address.Address.t)
  | BalanceTransfer
    (balance : ruint.Uint.t 256 4)
    (from : address.Address.t)
    (to : address.Address.t)
  | NonceChange
    (address : address.Address.t)
    (previous_nonce : U64.t)
  | NonceBump
    (address : address.Address.t)
  | AccountCreated
    (address : address.Address.t)
    (is_created_globally : bool)
  | StorageChanged
    (key : ruint.Uint.t 256 4)
    (had_value : ruint.Uint.t 256 4)
    (address : address.Address.t)
  | StorageWarmed
    (key : ruint.Uint.t 256 4)
    (address : address.Address.t)
  | TransientStorageChange
    (key : ruint.Uint.t 256 4)
    (had_value : ruint.Uint.t 256 4)
    (address : address.Address.t)
  | CodeChange
    (address : address.Address.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::journaled_state::entry::JournalEntry";
    φ x :=
      match x with
      | AccountWarmed address =>
        Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::AccountWarmed" [
          ("address", φ address)
        ]
      | AccountDestroyed had_balance address target destroyed_status =>
        Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::AccountDestroyed" [
          ("had_balance", φ had_balance);
          ("address", φ address);
          ("target", φ target);
          ("destroyed_status", φ destroyed_status)
        ]
      | AccountTouched address =>
        Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::AccountTouched" [
          ("address", φ address)
        ]
      | BalanceChange old_balance address =>
        Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::BalanceChange" [
          ("old_balance", φ old_balance);
          ("address", φ address)
        ]
      | BalanceTransfer balance from to =>
        Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::BalanceTransfer" [
          ("balance", φ balance);
          ("from", φ from);
          ("to", φ to)
        ]
      | NonceChange address previous_nonce =>
        Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::NonceChange" [
          ("address", φ address);
          ("previous_nonce", φ previous_nonce)
        ]
      | NonceBump address =>
        Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::NonceBump" [
          ("address", φ address)
        ]
      | AccountCreated address is_created_globally =>
        Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::AccountCreated" [
          ("address", φ address);
          ("is_created_globally", φ is_created_globally)
        ]
      | StorageChanged key had_value address =>
        Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::StorageChanged" [
          ("key", φ key);
          ("had_value", φ had_value);
          ("address", φ address)
        ]
      | StorageWarmed key address =>
        Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::StorageWarmed" [
          ("key", φ key);
          ("address", φ address)
        ]
      | TransientStorageChange key had_value address =>
        Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::TransientStorageChange" [
          ("key", φ key);
          ("had_value", φ had_value);
          ("address", φ address)
        ]
      | CodeChange address =>
        Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::CodeChange" [
          ("address", φ address)
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::journaled_state::entry::JournalEntry").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_AccountWarmed
    (address : address.Address.t) (address' : Value.t) :
    address' = φ address ->
    Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::AccountWarmed" [
      ("address", address')
    ] =
    φ (AccountWarmed address).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_AccountWarmed : of_value.

  Lemma of_value_with_AccountDestroyed
    (had_balance : ruint.Uint.t 256 4) (had_balance' : Value.t)
    (address : address.Address.t) (address' : Value.t)
    (target : address.Address.t) (target' : Value.t)
    (destroyed_status : entry.SelfdestructionRevertStatus.t) (destroyed_status' : Value.t) :
    had_balance' = φ had_balance ->
    address' = φ address ->
    target' = φ target ->
    destroyed_status' = φ destroyed_status ->
    Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::AccountDestroyed" [
      ("had_balance", had_balance');
      ("address", address');
      ("target", target');
      ("destroyed_status", destroyed_status')
    ] =
    φ (AccountDestroyed had_balance address target destroyed_status).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_AccountDestroyed : of_value.

  Lemma of_value_with_AccountTouched
    (address : address.Address.t) (address' : Value.t) :
    address' = φ address ->
    Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::AccountTouched" [
      ("address", address')
    ] =
    φ (AccountTouched address).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_AccountTouched : of_value.

  Lemma of_value_with_BalanceChange
    (old_balance : ruint.Uint.t 256 4) (old_balance' : Value.t)
    (address : address.Address.t) (address' : Value.t) :
    old_balance' = φ old_balance ->
    address' = φ address ->
    Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::BalanceChange" [
      ("old_balance", old_balance');
      ("address", address')
    ] =
    φ (BalanceChange old_balance address).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BalanceChange : of_value.

  Lemma of_value_with_BalanceTransfer
    (balance : ruint.Uint.t 256 4) (balance' : Value.t)
    (from : address.Address.t) (from' : Value.t)
    (to : address.Address.t) (to' : Value.t) :
    balance' = φ balance ->
    from' = φ from ->
    to' = φ to ->
    Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::BalanceTransfer" [
      ("balance", balance');
      ("from", from');
      ("to", to')
    ] =
    φ (BalanceTransfer balance from to).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BalanceTransfer : of_value.

  Lemma of_value_with_NonceChange
    (address : address.Address.t) (address' : Value.t)
    (previous_nonce : U64.t) (previous_nonce' : Value.t) :
    address' = φ address ->
    previous_nonce' = φ previous_nonce ->
    Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::NonceChange" [
      ("address", address');
      ("previous_nonce", previous_nonce')
    ] =
    φ (NonceChange address previous_nonce).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NonceChange : of_value.

  Lemma of_value_with_NonceBump
    (address : address.Address.t) (address' : Value.t) :
    address' = φ address ->
    Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::NonceBump" [
      ("address", address')
    ] =
    φ (NonceBump address).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NonceBump : of_value.

  Lemma of_value_with_AccountCreated
    (address : address.Address.t) (address' : Value.t)
    (is_created_globally : bool) (is_created_globally' : Value.t) :
    address' = φ address ->
    is_created_globally' = φ is_created_globally ->
    Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::AccountCreated" [
      ("address", address');
      ("is_created_globally", is_created_globally')
    ] =
    φ (AccountCreated address is_created_globally).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_AccountCreated : of_value.

  Lemma of_value_with_StorageChanged
    (key : ruint.Uint.t 256 4) (key' : Value.t)
    (had_value : ruint.Uint.t 256 4) (had_value' : Value.t)
    (address : address.Address.t) (address' : Value.t) :
    key' = φ key ->
    had_value' = φ had_value ->
    address' = φ address ->
    Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::StorageChanged" [
      ("key", key');
      ("had_value", had_value');
      ("address", address')
    ] =
    φ (StorageChanged key had_value address).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StorageChanged : of_value.

  Lemma of_value_with_StorageWarmed
    (key : ruint.Uint.t 256 4) (key' : Value.t)
    (address : address.Address.t) (address' : Value.t) :
    key' = φ key ->
    address' = φ address ->
    Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::StorageWarmed" [
      ("key", key');
      ("address", address')
    ] =
    φ (StorageWarmed key address).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StorageWarmed : of_value.

  Lemma of_value_with_TransientStorageChange
    (key : ruint.Uint.t 256 4) (key' : Value.t)
    (had_value : ruint.Uint.t 256 4) (had_value' : Value.t)
    (address : address.Address.t) (address' : Value.t) :
    key' = φ key ->
    had_value' = φ had_value ->
    address' = φ address ->
    Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::TransientStorageChange" [
      ("key", key');
      ("had_value", had_value');
      ("address", address')
    ] =
    φ (TransientStorageChange key had_value address).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_TransientStorageChange : of_value.

  Lemma of_value_with_CodeChange
    (address : address.Address.t) (address' : Value.t) :
    address' = φ address ->
    Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::CodeChange" [
      ("address", address')
    ] =
    φ (CodeChange address).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CodeChange : of_value.

  Definition of_value_AccountWarmed
    (address : address.Address.t) (address' : Value.t) :
    address' = φ address ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::AccountWarmed" [
        ("address", address')
      ]
    ).
  Proof. econstructor; apply of_value_with_AccountWarmed; eassumption. Defined.
  Smpl Add simple apply of_value_AccountWarmed : of_value.

  Definition of_value_AccountDestroyed
    (had_balance : ruint.Uint.t 256 4) (had_balance' : Value.t)
    (address : address.Address.t) (address' : Value.t)
    (target : address.Address.t) (target' : Value.t)
    (destroyed_status : entry.SelfdestructionRevertStatus.t) (destroyed_status' : Value.t) :
    had_balance' = φ had_balance ->
    address' = φ address ->
    target' = φ target ->
    destroyed_status' = φ destroyed_status ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::AccountDestroyed" [
        ("had_balance", had_balance');
        ("address", address');
        ("target", target');
        ("destroyed_status", destroyed_status')
      ]
    ).
  Proof. econstructor; apply of_value_with_AccountDestroyed; eassumption. Defined.
  Smpl Add simple apply of_value_AccountDestroyed : of_value.

  Definition of_value_AccountTouched
    (address : address.Address.t) (address' : Value.t) :
    address' = φ address ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::AccountTouched" [
        ("address", address')
      ]
    ).
  Proof. econstructor; apply of_value_with_AccountTouched; eassumption. Defined.
  Smpl Add simple apply of_value_AccountTouched : of_value.

  Definition of_value_BalanceChange
    (old_balance : ruint.Uint.t 256 4) (old_balance' : Value.t)
    (address : address.Address.t) (address' : Value.t) :
    old_balance' = φ old_balance ->
    address' = φ address ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::BalanceChange" [
        ("old_balance", old_balance');
        ("address", address')
      ]
    ).
  Proof. econstructor; apply of_value_with_BalanceChange; eassumption. Defined.
  Smpl Add simple apply of_value_BalanceChange : of_value.

  Definition of_value_BalanceTransfer
    (balance : ruint.Uint.t 256 4) (balance' : Value.t)
    (from : address.Address.t) (from' : Value.t)
    (to : address.Address.t) (to' : Value.t) :
    balance' = φ balance ->
    from' = φ from ->
    to' = φ to ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::BalanceTransfer" [
        ("balance", balance');
        ("from", from');
        ("to", to')
      ]
    ).
  Proof. econstructor; apply of_value_with_BalanceTransfer; eassumption. Defined.
  Smpl Add simple apply of_value_BalanceTransfer : of_value.

  Definition of_value_NonceChange
    (address : address.Address.t) (address' : Value.t)
    (previous_nonce : U64.t) (previous_nonce' : Value.t) :
    address' = φ address ->
    previous_nonce' = φ previous_nonce ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::NonceChange" [
        ("address", address');
        ("previous_nonce", previous_nonce')
      ]
    ).
  Proof. econstructor; apply of_value_with_NonceChange; eassumption. Defined.
  Smpl Add simple apply of_value_NonceChange : of_value.

  Definition of_value_NonceBump
    (address : address.Address.t) (address' : Value.t) :
    address' = φ address ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::NonceBump" [
        ("address", address')
      ]
    ).
  Proof. econstructor; apply of_value_with_NonceBump; eassumption. Defined.
  Smpl Add simple apply of_value_NonceBump : of_value.

  Definition of_value_AccountCreated
    (address : address.Address.t) (address' : Value.t)
    (is_created_globally : bool) (is_created_globally' : Value.t) :
    address' = φ address ->
    is_created_globally' = φ is_created_globally ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::AccountCreated" [
        ("address", address');
        ("is_created_globally", is_created_globally')
      ]
    ).
  Proof. econstructor; apply of_value_with_AccountCreated; eassumption. Defined.
  Smpl Add simple apply of_value_AccountCreated : of_value.

  Definition of_value_StorageChanged
    (key : ruint.Uint.t 256 4) (key' : Value.t)
    (had_value : ruint.Uint.t 256 4) (had_value' : Value.t)
    (address : address.Address.t) (address' : Value.t) :
    key' = φ key ->
    had_value' = φ had_value ->
    address' = φ address ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::StorageChanged" [
        ("key", key');
        ("had_value", had_value');
        ("address", address')
      ]
    ).
  Proof. econstructor; apply of_value_with_StorageChanged; eassumption. Defined.
  Smpl Add simple apply of_value_StorageChanged : of_value.

  Definition of_value_StorageWarmed
    (key : ruint.Uint.t 256 4) (key' : Value.t)
    (address : address.Address.t) (address' : Value.t) :
    key' = φ key ->
    address' = φ address ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::StorageWarmed" [
        ("key", key');
        ("address", address')
      ]
    ).
  Proof. econstructor; apply of_value_with_StorageWarmed; eassumption. Defined.
  Smpl Add simple apply of_value_StorageWarmed : of_value.

  Definition of_value_TransientStorageChange
    (key : ruint.Uint.t 256 4) (key' : Value.t)
    (had_value : ruint.Uint.t 256 4) (had_value' : Value.t)
    (address : address.Address.t) (address' : Value.t) :
    key' = φ key ->
    had_value' = φ had_value ->
    address' = φ address ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::TransientStorageChange" [
        ("key", key');
        ("had_value", had_value');
        ("address", address')
      ]
    ).
  Proof. econstructor; apply of_value_with_TransientStorageChange; eassumption. Defined.
  Smpl Add simple apply of_value_TransientStorageChange : of_value.

  Definition of_value_CodeChange
    (address : address.Address.t) (address' : Value.t) :
    address' = φ address ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::CodeChange" [
        ("address", address')
      ]
    ).
  Proof. econstructor; apply of_value_with_CodeChange; eassumption. Defined.
  Smpl Add simple apply of_value_CodeChange : of_value.

  Module SubPointer.
    Definition get_AccountWarmed_address : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::AccountWarmed" "address") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | AccountWarmed γ_address => Some γ_address
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_address : address.Address.t) :=
        match γ with
        | AccountWarmed _ => Some (AccountWarmed γ_address)
        | _ => None
        end;
    |}.

    Lemma get_AccountWarmed_address_is_valid : SubPointer.Runner.Valid.t get_AccountWarmed_address.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_AccountWarmed_address_is_valid : run_sub_pointer.

    Definition get_AccountDestroyed_had_balance : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::AccountDestroyed" "had_balance") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | AccountDestroyed γ_had_balance _ _ _ => Some γ_had_balance
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_had_balance : ruint.Uint.t 256 4) :=
        match γ with
        | AccountDestroyed _ γ_address γ_target γ_destroyed_status => Some (AccountDestroyed γ_had_balance γ_address γ_target γ_destroyed_status)
        | _ => None
        end;
    |}.

    Lemma get_AccountDestroyed_had_balance_is_valid : SubPointer.Runner.Valid.t get_AccountDestroyed_had_balance.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_AccountDestroyed_had_balance_is_valid : run_sub_pointer.

    Definition get_AccountDestroyed_address : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::AccountDestroyed" "address") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | AccountDestroyed _ γ_address _ _ => Some γ_address
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_address : address.Address.t) :=
        match γ with
        | AccountDestroyed γ_had_balance _ γ_target γ_destroyed_status => Some (AccountDestroyed γ_had_balance γ_address γ_target γ_destroyed_status)
        | _ => None
        end;
    |}.

    Lemma get_AccountDestroyed_address_is_valid : SubPointer.Runner.Valid.t get_AccountDestroyed_address.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_AccountDestroyed_address_is_valid : run_sub_pointer.

    Definition get_AccountDestroyed_target : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::AccountDestroyed" "target") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | AccountDestroyed _ _ γ_target _ => Some γ_target
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_target : address.Address.t) :=
        match γ with
        | AccountDestroyed γ_had_balance γ_address _ γ_destroyed_status => Some (AccountDestroyed γ_had_balance γ_address γ_target γ_destroyed_status)
        | _ => None
        end;
    |}.

    Lemma get_AccountDestroyed_target_is_valid : SubPointer.Runner.Valid.t get_AccountDestroyed_target.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_AccountDestroyed_target_is_valid : run_sub_pointer.

    Definition get_AccountDestroyed_destroyed_status : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::AccountDestroyed" "destroyed_status") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | AccountDestroyed _ _ _ γ_destroyed_status => Some γ_destroyed_status
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_destroyed_status : entry.SelfdestructionRevertStatus.t) :=
        match γ with
        | AccountDestroyed γ_had_balance γ_address γ_target _ => Some (AccountDestroyed γ_had_balance γ_address γ_target γ_destroyed_status)
        | _ => None
        end;
    |}.

    Lemma get_AccountDestroyed_destroyed_status_is_valid : SubPointer.Runner.Valid.t get_AccountDestroyed_destroyed_status.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_AccountDestroyed_destroyed_status_is_valid : run_sub_pointer.

    Definition get_AccountTouched_address : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::AccountTouched" "address") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | AccountTouched γ_address => Some γ_address
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_address : address.Address.t) :=
        match γ with
        | AccountTouched _ => Some (AccountTouched γ_address)
        | _ => None
        end;
    |}.

    Lemma get_AccountTouched_address_is_valid : SubPointer.Runner.Valid.t get_AccountTouched_address.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_AccountTouched_address_is_valid : run_sub_pointer.

    Definition get_BalanceChange_old_balance : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::BalanceChange" "old_balance") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | BalanceChange γ_old_balance _ => Some γ_old_balance
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_old_balance : ruint.Uint.t 256 4) :=
        match γ with
        | BalanceChange _ γ_address => Some (BalanceChange γ_old_balance γ_address)
        | _ => None
        end;
    |}.

    Lemma get_BalanceChange_old_balance_is_valid : SubPointer.Runner.Valid.t get_BalanceChange_old_balance.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_BalanceChange_old_balance_is_valid : run_sub_pointer.

    Definition get_BalanceChange_address : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::BalanceChange" "address") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | BalanceChange _ γ_address => Some γ_address
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_address : address.Address.t) :=
        match γ with
        | BalanceChange γ_old_balance _ => Some (BalanceChange γ_old_balance γ_address)
        | _ => None
        end;
    |}.

    Lemma get_BalanceChange_address_is_valid : SubPointer.Runner.Valid.t get_BalanceChange_address.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_BalanceChange_address_is_valid : run_sub_pointer.

    Definition get_BalanceTransfer_balance : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::BalanceTransfer" "balance") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | BalanceTransfer γ_balance _ _ => Some γ_balance
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_balance : ruint.Uint.t 256 4) :=
        match γ with
        | BalanceTransfer _ γ_from γ_to => Some (BalanceTransfer γ_balance γ_from γ_to)
        | _ => None
        end;
    |}.

    Lemma get_BalanceTransfer_balance_is_valid : SubPointer.Runner.Valid.t get_BalanceTransfer_balance.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_BalanceTransfer_balance_is_valid : run_sub_pointer.

    Definition get_BalanceTransfer_from : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::BalanceTransfer" "from") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | BalanceTransfer _ γ_from _ => Some γ_from
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_from : address.Address.t) :=
        match γ with
        | BalanceTransfer γ_balance _ γ_to => Some (BalanceTransfer γ_balance γ_from γ_to)
        | _ => None
        end;
    |}.

    Lemma get_BalanceTransfer_from_is_valid : SubPointer.Runner.Valid.t get_BalanceTransfer_from.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_BalanceTransfer_from_is_valid : run_sub_pointer.

    Definition get_BalanceTransfer_to : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::BalanceTransfer" "to") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | BalanceTransfer _ _ γ_to => Some γ_to
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_to : address.Address.t) :=
        match γ with
        | BalanceTransfer γ_balance γ_from _ => Some (BalanceTransfer γ_balance γ_from γ_to)
        | _ => None
        end;
    |}.

    Lemma get_BalanceTransfer_to_is_valid : SubPointer.Runner.Valid.t get_BalanceTransfer_to.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_BalanceTransfer_to_is_valid : run_sub_pointer.

    Definition get_NonceChange_address : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::NonceChange" "address") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | NonceChange γ_address _ => Some γ_address
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_address : address.Address.t) :=
        match γ with
        | NonceChange _ γ_previous_nonce => Some (NonceChange γ_address γ_previous_nonce)
        | _ => None
        end;
    |}.

    Lemma get_NonceChange_address_is_valid : SubPointer.Runner.Valid.t get_NonceChange_address.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_NonceChange_address_is_valid : run_sub_pointer.

    Definition get_NonceChange_previous_nonce : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::NonceChange" "previous_nonce") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | NonceChange _ γ_previous_nonce => Some γ_previous_nonce
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_previous_nonce : U64.t) :=
        match γ with
        | NonceChange γ_address _ => Some (NonceChange γ_address γ_previous_nonce)
        | _ => None
        end;
    |}.

    Lemma get_NonceChange_previous_nonce_is_valid : SubPointer.Runner.Valid.t get_NonceChange_previous_nonce.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_NonceChange_previous_nonce_is_valid : run_sub_pointer.

    Definition get_NonceBump_address : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::NonceBump" "address") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | NonceBump γ_address => Some γ_address
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_address : address.Address.t) :=
        match γ with
        | NonceBump _ => Some (NonceBump γ_address)
        | _ => None
        end;
    |}.

    Lemma get_NonceBump_address_is_valid : SubPointer.Runner.Valid.t get_NonceBump_address.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_NonceBump_address_is_valid : run_sub_pointer.

    Definition get_AccountCreated_address : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::AccountCreated" "address") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | AccountCreated γ_address _ => Some γ_address
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_address : address.Address.t) :=
        match γ with
        | AccountCreated _ γ_is_created_globally => Some (AccountCreated γ_address γ_is_created_globally)
        | _ => None
        end;
    |}.

    Lemma get_AccountCreated_address_is_valid : SubPointer.Runner.Valid.t get_AccountCreated_address.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_AccountCreated_address_is_valid : run_sub_pointer.

    Definition get_AccountCreated_is_created_globally : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::AccountCreated" "is_created_globally") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | AccountCreated _ γ_is_created_globally => Some γ_is_created_globally
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_is_created_globally : bool) :=
        match γ with
        | AccountCreated γ_address _ => Some (AccountCreated γ_address γ_is_created_globally)
        | _ => None
        end;
    |}.

    Lemma get_AccountCreated_is_created_globally_is_valid : SubPointer.Runner.Valid.t get_AccountCreated_is_created_globally.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_AccountCreated_is_created_globally_is_valid : run_sub_pointer.

    Definition get_StorageChanged_key : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::StorageChanged" "key") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | StorageChanged γ_key _ _ => Some γ_key
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_key : ruint.Uint.t 256 4) :=
        match γ with
        | StorageChanged _ γ_had_value γ_address => Some (StorageChanged γ_key γ_had_value γ_address)
        | _ => None
        end;
    |}.

    Lemma get_StorageChanged_key_is_valid : SubPointer.Runner.Valid.t get_StorageChanged_key.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_StorageChanged_key_is_valid : run_sub_pointer.

    Definition get_StorageChanged_had_value : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::StorageChanged" "had_value") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | StorageChanged _ γ_had_value _ => Some γ_had_value
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_had_value : ruint.Uint.t 256 4) :=
        match γ with
        | StorageChanged γ_key _ γ_address => Some (StorageChanged γ_key γ_had_value γ_address)
        | _ => None
        end;
    |}.

    Lemma get_StorageChanged_had_value_is_valid : SubPointer.Runner.Valid.t get_StorageChanged_had_value.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_StorageChanged_had_value_is_valid : run_sub_pointer.

    Definition get_StorageChanged_address : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::StorageChanged" "address") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | StorageChanged _ _ γ_address => Some γ_address
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_address : address.Address.t) :=
        match γ with
        | StorageChanged γ_key γ_had_value _ => Some (StorageChanged γ_key γ_had_value γ_address)
        | _ => None
        end;
    |}.

    Lemma get_StorageChanged_address_is_valid : SubPointer.Runner.Valid.t get_StorageChanged_address.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_StorageChanged_address_is_valid : run_sub_pointer.

    Definition get_StorageWarmed_key : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::StorageWarmed" "key") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | StorageWarmed γ_key _ => Some γ_key
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_key : ruint.Uint.t 256 4) :=
        match γ with
        | StorageWarmed _ γ_address => Some (StorageWarmed γ_key γ_address)
        | _ => None
        end;
    |}.

    Lemma get_StorageWarmed_key_is_valid : SubPointer.Runner.Valid.t get_StorageWarmed_key.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_StorageWarmed_key_is_valid : run_sub_pointer.

    Definition get_StorageWarmed_address : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::StorageWarmed" "address") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | StorageWarmed _ γ_address => Some γ_address
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_address : address.Address.t) :=
        match γ with
        | StorageWarmed γ_key _ => Some (StorageWarmed γ_key γ_address)
        | _ => None
        end;
    |}.

    Lemma get_StorageWarmed_address_is_valid : SubPointer.Runner.Valid.t get_StorageWarmed_address.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_StorageWarmed_address_is_valid : run_sub_pointer.

    Definition get_TransientStorageChange_key : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::TransientStorageChange" "key") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | TransientStorageChange γ_key _ _ => Some γ_key
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_key : ruint.Uint.t 256 4) :=
        match γ with
        | TransientStorageChange _ γ_had_value γ_address => Some (TransientStorageChange γ_key γ_had_value γ_address)
        | _ => None
        end;
    |}.

    Lemma get_TransientStorageChange_key_is_valid : SubPointer.Runner.Valid.t get_TransientStorageChange_key.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_TransientStorageChange_key_is_valid : run_sub_pointer.

    Definition get_TransientStorageChange_had_value : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::TransientStorageChange" "had_value") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | TransientStorageChange _ γ_had_value _ => Some γ_had_value
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_had_value : ruint.Uint.t 256 4) :=
        match γ with
        | TransientStorageChange γ_key _ γ_address => Some (TransientStorageChange γ_key γ_had_value γ_address)
        | _ => None
        end;
    |}.

    Lemma get_TransientStorageChange_had_value_is_valid : SubPointer.Runner.Valid.t get_TransientStorageChange_had_value.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_TransientStorageChange_had_value_is_valid : run_sub_pointer.

    Definition get_TransientStorageChange_address : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::TransientStorageChange" "address") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | TransientStorageChange _ _ γ_address => Some γ_address
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_address : address.Address.t) :=
        match γ with
        | TransientStorageChange γ_key γ_had_value _ => Some (TransientStorageChange γ_key γ_had_value γ_address)
        | _ => None
        end;
    |}.

    Lemma get_TransientStorageChange_address_is_valid : SubPointer.Runner.Valid.t get_TransientStorageChange_address.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_TransientStorageChange_address_is_valid : run_sub_pointer.

    Definition get_CodeChange_address : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::entry::JournalEntry::CodeChange" "address") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | CodeChange γ_address => Some γ_address
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_address : address.Address.t) :=
        match γ with
        | CodeChange _ => Some (CodeChange γ_address)
        | _ => None
        end;
    |}.

    Lemma get_CodeChange_address_is_valid : SubPointer.Runner.Valid.t get_CodeChange_address.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_CodeChange_address_is_valid : run_sub_pointer.
  End SubPointer.
End JournalEntry.

Module TransactionType.
  Inductive t : Set :=
  | Legacy
  | Eip2930
  | Eip1559
  | Eip4844
  | Eip7702
  | Custom
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::transaction::transaction_type::TransactionType";
    φ x :=
      match x with
      | Legacy =>
        Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Legacy" []
      | Eip2930 =>
        Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip2930" []
      | Eip1559 =>
        Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip1559" []
      | Eip4844 =>
        Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip4844" []
      | Eip7702 =>
        Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip7702" []
      | Custom =>
        Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Custom" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::transaction::transaction_type::TransactionType").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Legacy :
    Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Legacy" [] =
    φ Legacy.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Legacy : of_value.

  Lemma of_value_with_Eip2930 :
    Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip2930" [] =
    φ Eip2930.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip2930 : of_value.

  Lemma of_value_with_Eip1559 :
    Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip1559" [] =
    φ Eip1559.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip1559 : of_value.

  Lemma of_value_with_Eip4844 :
    Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip4844" [] =
    φ Eip4844.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip4844 : of_value.

  Lemma of_value_with_Eip7702 :
    Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip7702" [] =
    φ Eip7702.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip7702 : of_value.

  Lemma of_value_with_Custom :
    Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Custom" [] =
    φ Custom.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Custom : of_value.

  Definition of_value_Legacy :
    OfValue.t (
      Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Legacy" []
    ).
  Proof. econstructor; apply of_value_with_Legacy; eassumption. Defined.
  Smpl Add simple apply of_value_Legacy : of_value.

  Definition of_value_Eip2930 :
    OfValue.t (
      Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip2930" []
    ).
  Proof. econstructor; apply of_value_with_Eip2930; eassumption. Defined.
  Smpl Add simple apply of_value_Eip2930 : of_value.

  Definition of_value_Eip1559 :
    OfValue.t (
      Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip1559" []
    ).
  Proof. econstructor; apply of_value_with_Eip1559; eassumption. Defined.
  Smpl Add simple apply of_value_Eip1559 : of_value.

  Definition of_value_Eip4844 :
    OfValue.t (
      Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip4844" []
    ).
  Proof. econstructor; apply of_value_with_Eip4844; eassumption. Defined.
  Smpl Add simple apply of_value_Eip4844 : of_value.

  Definition of_value_Eip7702 :
    OfValue.t (
      Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip7702" []
    ).
  Proof. econstructor; apply of_value_with_Eip7702; eassumption. Defined.
  Smpl Add simple apply of_value_Eip7702 : of_value.

  Definition of_value_Custom :
    OfValue.t (
      Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Custom" []
    ).
  Proof. econstructor; apply of_value_with_Custom; eassumption. Defined.
  Smpl Add simple apply of_value_Custom : of_value.

  Module SubPointer.

  End SubPointer.
End TransactionType.

Module EmptyDBTyped.
  Record t {E: Set} : Set := {
    _phantom: marker.PhantomData.t E;
  }.
  Arguments Build_t {_}.
  Arguments t : clear implicits.

  Global Instance IsLink {E: Set} `{Link E} : Link (t E) := {
    Φ := Ty.path "revm_database_interface::empty_db::EmptyDBTyped";
    φ '(Build_t _phantom) :=
      Value.StructRecord "revm_database_interface::empty_db::EmptyDBTyped" [
        ("_phantom", φ _phantom)
      ]
  }.
End EmptyDBTyped.

Module EthFrame.
  Record t {IW: Set} : Set := {
    data: frame_data.FrameData.t;
    input: interpreter_action.FrameInput.t;
    depth: Usize.t;
    checkpoint: journaled_state.JournalCheckpoint.t;
    interpreter: interpreter.Interpreter.t IW;
    is_finished: bool;
  }.
  Arguments Build_t {_}.
  Arguments t : clear implicits.

  Global Instance IsLink {IW: Set} `{Link IW} : Link (t IW) := {
    Φ := Ty.path "revm_handler::frame::EthFrame";
    φ '(Build_t data input depth checkpoint interpreter is_finished) :=
      Value.StructRecord "revm_handler::frame::EthFrame" [
        ("data", φ data);
        ("input", φ input);
        ("depth", φ depth);
        ("checkpoint", φ checkpoint);
        ("interpreter", φ interpreter);
        ("is_finished", φ is_finished)
      ]
  }.
End EthFrame.

Module CallFrame.
  Record t : Set := {
    return_memory_range: range.Range.t Usize.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_handler::frame_data::CallFrame";
    φ '(Build_t return_memory_range) :=
      Value.StructRecord "revm_handler::frame_data::CallFrame" [
        ("return_memory_range", φ return_memory_range)
      ]
  }.
End CallFrame.

Module CreateFrame.
  Record t : Set := {
    created_address: address.Address.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_handler::frame_data::CreateFrame";
    φ '(Build_t created_address) :=
      Value.StructRecord "revm_handler::frame_data::CreateFrame" [
        ("created_address", φ created_address)
      ]
  }.
End CreateFrame.

Module FrameData.
  Inductive t : Set :=
  | Call
    (_ : frame_data.CallFrame.t)
  | Create
    (_ : frame_data.CreateFrame.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_handler::frame_data::FrameData";
    φ x :=
      match x with
      | Call γ0 =>
        Value.StructTuple "revm_handler::frame_data::FrameData::Call" [
          φ γ0
        ]
      | Create γ0 =>
        Value.StructTuple "revm_handler::frame_data::FrameData::Create" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_handler::frame_data::FrameData").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Call
    (γ0 : frame_data.CallFrame.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_handler::frame_data::FrameData::Call" [
      γ0
    ] =
    φ (Call γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Call : of_value.

  Lemma of_value_with_Create
    (γ0 : frame_data.CreateFrame.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_handler::frame_data::FrameData::Create" [
      γ0
    ] =
    φ (Create γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Create : of_value.

  Definition of_value_Call
    (γ0 : frame_data.CallFrame.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_handler::frame_data::FrameData::Call" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Call; eassumption. Defined.
  Smpl Add simple apply of_value_Call : of_value.

  Definition of_value_Create
    (γ0 : frame_data.CreateFrame.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_handler::frame_data::FrameData::Create" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Create; eassumption. Defined.
  Smpl Add simple apply of_value_Create : of_value.

  Module SubPointer.
    Definition get_Call_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_handler::frame_data::FrameData::Call" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Call γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : frame_data.CallFrame.t) :=
        match γ with
        | Call _ => Some (Call γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Call_0_is_valid : SubPointer.Runner.Valid.t get_Call_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Call_0_is_valid : run_sub_pointer.

    Definition get_Create_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_handler::frame_data::FrameData::Create" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Create γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : frame_data.CreateFrame.t) :=
        match γ with
        | Create _ => Some (Create γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Create_0_is_valid : SubPointer.Runner.Valid.t get_Create_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Create_0_is_valid : run_sub_pointer.
  End SubPointer.
End FrameData.

Module FrameResult.
  Inductive t : Set :=
  | Call
    (_ : call_outcome.CallOutcome.t)
  | Create
    (_ : create_outcome.CreateOutcome.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_handler::frame_data::FrameResult";
    φ x :=
      match x with
      | Call γ0 =>
        Value.StructTuple "revm_handler::frame_data::FrameResult::Call" [
          φ γ0
        ]
      | Create γ0 =>
        Value.StructTuple "revm_handler::frame_data::FrameResult::Create" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_handler::frame_data::FrameResult").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Call
    (γ0 : call_outcome.CallOutcome.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_handler::frame_data::FrameResult::Call" [
      γ0
    ] =
    φ (Call γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Call : of_value.

  Lemma of_value_with_Create
    (γ0 : create_outcome.CreateOutcome.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_handler::frame_data::FrameResult::Create" [
      γ0
    ] =
    φ (Create γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Create : of_value.

  Definition of_value_Call
    (γ0 : call_outcome.CallOutcome.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_handler::frame_data::FrameResult::Call" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Call; eassumption. Defined.
  Smpl Add simple apply of_value_Call : of_value.

  Definition of_value_Create
    (γ0 : create_outcome.CreateOutcome.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_handler::frame_data::FrameResult::Create" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Create; eassumption. Defined.
  Smpl Add simple apply of_value_Create : of_value.

  Module SubPointer.
    Definition get_Call_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_handler::frame_data::FrameResult::Call" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Call γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : call_outcome.CallOutcome.t) :=
        match γ with
        | Call _ => Some (Call γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Call_0_is_valid : SubPointer.Runner.Valid.t get_Call_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Call_0_is_valid : run_sub_pointer.

    Definition get_Create_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_handler::frame_data::FrameResult::Create" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Create γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : create_outcome.CreateOutcome.t) :=
        match γ with
        | Create _ => Some (Create γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Create_0_is_valid : SubPointer.Runner.Valid.t get_Create_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Create_0_is_valid : run_sub_pointer.
  End SubPointer.
End FrameResult.

Module EthInstructions.
  Record t {WIRE HOST: Set} : Set := {
    instruction_table: boxed.Box.t (array.t 256 (instructions.Instruction.t WIRE HOST)) alloc.Global.t;
  }.
  Arguments Build_t {_ _}.
  Arguments t : clear implicits.

  Global Instance IsLink {WIRE HOST: Set} `{Link WIRE} `{Link HOST} : Link (t WIRE HOST) := {
    Φ := Ty.path "revm_handler::instructions::EthInstructions";
    φ '(Build_t instruction_table) :=
      Value.StructRecord "revm_handler::instructions::EthInstructions" [
        ("instruction_table", φ instruction_table)
      ]
  }.
End EthInstructions.

Module ItemOrResult.
  Inductive t (ITEM RES: Set) : Set :=
  | Item
    (_ : ITEM)
  | Result
    (_ : RES)
  .
  Arguments Item Result {_ _}.

  Global Instance IsLink (ITEM RES: Set) : Link t ITEM RES := {
    Φ := Ty.path "revm_handler::item_or_result::ItemOrResult";
    φ x :=
      match x with
      | Item γ0 =>
        Value.StructTuple "revm_handler::item_or_result::ItemOrResult::Item" [
          φ γ0
        ]
      | Result γ0 =>
        Value.StructTuple "revm_handler::item_or_result::ItemOrResult::Result" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_handler::item_or_result::ItemOrResult").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Item
    (γ0 : ITEM) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_handler::item_or_result::ItemOrResult::Item" [
      γ0
    ] =
    φ (Item γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Item : of_value.

  Lemma of_value_with_Result
    (γ0 : RES) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_handler::item_or_result::ItemOrResult::Result" [
      γ0
    ] =
    φ (Result γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Result : of_value.

  Definition of_value_Item
    (γ0 : ITEM) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_handler::item_or_result::ItemOrResult::Item" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Item; eassumption. Defined.
  Smpl Add simple apply of_value_Item : of_value.

  Definition of_value_Result
    (γ0 : RES) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_handler::item_or_result::ItemOrResult::Result" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Result; eassumption. Defined.
  Smpl Add simple apply of_value_Result : of_value.

  Module SubPointer.
    Definition get_Item_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_handler::item_or_result::ItemOrResult::Item" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Item γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : ITEM) :=
        match γ with
        | Item _ => Some (Item γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Item_0_is_valid : SubPointer.Runner.Valid.t get_Item_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Item_0_is_valid : run_sub_pointer.

    Definition get_Result_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_handler::item_or_result::ItemOrResult::Result" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Result γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : RES) :=
        match γ with
        | Result _ => Some (Result γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Result_0_is_valid : SubPointer.Runner.Valid.t get_Result_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Result_0_is_valid : run_sub_pointer.
  End SubPointer.
End ItemOrResult.

Module MainnetHandler.
  Record t {CTX ERROR FRAME: Set} : Set := {
    _phantom: marker.PhantomData.t (CTX * ERROR * FRAME);
  }.
  Arguments Build_t {_ _ _}.
  Arguments t : clear implicits.

  Global Instance IsLink {CTX ERROR FRAME: Set} `{Link CTX} `{Link ERROR} `{Link FRAME} : Link (t CTX ERROR FRAME) := {
    Φ := Ty.path "revm_handler::mainnet_handler::MainnetHandler";
    φ '(Build_t _phantom) :=
      Value.StructRecord "revm_handler::mainnet_handler::MainnetHandler" [
        ("_phantom", φ _phantom)
      ]
  }.
End MainnetHandler.

Module EthPrecompiles.
  Record t : Set := {
    precompiles: '& revm_precompile.Precompiles.t;
    spec: hardfork.SpecId.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_handler::precompile_provider::EthPrecompiles";
    φ '(Build_t precompiles spec) :=
      Value.StructRecord "revm_handler::precompile_provider::EthPrecompiles" [
        ("precompiles", φ precompiles);
        ("spec", φ spec)
      ]
  }.
End EthPrecompiles.

Module Gas.
  Record t : Set := {
    limit: U64.t;
    remaining: U64.t;
    refunded: I64.t;
    memory: gas.MemoryGas.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::gas::Gas";
    φ '(Build_t limit remaining refunded memory) :=
      Value.StructRecord "revm_interpreter::gas::Gas" [
        ("limit", φ limit);
        ("remaining", φ remaining);
        ("refunded", φ refunded);
        ("memory", φ memory)
      ]
  }.
End Gas.

Module MemoryExtensionResult.
  Inductive t : Set :=
  | Extended
  | Same
  | OutOfGas
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::gas::MemoryExtensionResult";
    φ x :=
      match x with
      | Extended =>
        Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::Extended" []
      | Same =>
        Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::Same" []
      | OutOfGas =>
        Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::OutOfGas" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::gas::MemoryExtensionResult").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Extended :
    Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::Extended" [] =
    φ Extended.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Extended : of_value.

  Lemma of_value_with_Same :
    Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::Same" [] =
    φ Same.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Same : of_value.

  Lemma of_value_with_OutOfGas :
    Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::OutOfGas" [] =
    φ OutOfGas.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfGas : of_value.

  Definition of_value_Extended :
    OfValue.t (
      Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::Extended" []
    ).
  Proof. econstructor; apply of_value_with_Extended; eassumption. Defined.
  Smpl Add simple apply of_value_Extended : of_value.

  Definition of_value_Same :
    OfValue.t (
      Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::Same" []
    ).
  Proof. econstructor; apply of_value_with_Same; eassumption. Defined.
  Smpl Add simple apply of_value_Same : of_value.

  Definition of_value_OutOfGas :
    OfValue.t (
      Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::OutOfGas" []
    ).
  Proof. econstructor; apply of_value_with_OutOfGas; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfGas : of_value.

  Module SubPointer.

  End SubPointer.
End MemoryExtensionResult.

Module MemoryGas.
  Record t : Set := {
    words_num: Usize.t;
    expansion_cost: U64.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::gas::MemoryGas";
    φ '(Build_t words_num expansion_cost) :=
      Value.StructRecord "revm_interpreter::gas::MemoryGas" [
        ("words_num", φ words_num);
        ("expansion_cost", φ expansion_cost)
      ]
  }.
End MemoryGas.

Module InstructionContext.
  Record t {H ITy: Set} : Set := {
    interpreter: '&mut (interpreter.Interpreter.t ITy);
    host: '&mut H;
  }.
  Arguments Build_t {_ _}.
  Arguments t : clear implicits.

  Global Instance IsLink {H ITy: Set} `{Link H} `{Link ITy} : Link (t H ITy) := {
    Φ := Ty.path "revm_interpreter::instruction_context::InstructionContext";
    φ '(Build_t interpreter host) :=
      Value.StructRecord "revm_interpreter::instruction_context::InstructionContext" [
        ("interpreter", φ interpreter);
        ("host", φ host)
      ]
  }.
End InstructionContext.

Module InstructionResult.
  Inductive t : Set :=
  | Stop
  | Return
  | SelfDestruct
  | Revert
  | CallTooDeep
  | OutOfFunds
  | CreateInitCodeStartingEF00
  | InvalidEOFInitCode
  | InvalidExtDelegateCallTarget
  | OutOfGas
  | MemoryOOG
  | MemoryLimitOOG
  | PrecompileOOG
  | InvalidOperandOOG
  | ReentrancySentryOOG
  | OpcodeNotFound
  | CallNotAllowedInsideStatic
  | StateChangeDuringStaticCall
  | InvalidFEOpcode
  | InvalidJump
  | NotActivated
  | StackUnderflow
  | StackOverflow
  | OutOfOffset
  | CreateCollision
  | OverflowPayment
  | PrecompileError
  | NonceOverflow
  | CreateContractSizeLimit
  | CreateContractStartingWithEF
  | CreateInitCodeSizeLimit
  | FatalExternalError
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::instruction_result::InstructionResult";
    φ x :=
      match x with
      | Stop =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Stop" []
      | Return =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Return" []
      | SelfDestruct =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::SelfDestruct" []
      | Revert =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Revert" []
      | CallTooDeep =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallTooDeep" []
      | OutOfFunds =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfFunds" []
      | CreateInitCodeStartingEF00 =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeStartingEF00" []
      | InvalidEOFInitCode =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidEOFInitCode" []
      | InvalidExtDelegateCallTarget =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidExtDelegateCallTarget" []
      | OutOfGas =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfGas" []
      | MemoryOOG =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryOOG" []
      | MemoryLimitOOG =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryLimitOOG" []
      | PrecompileOOG =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileOOG" []
      | InvalidOperandOOG =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidOperandOOG" []
      | ReentrancySentryOOG =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReentrancySentryOOG" []
      | OpcodeNotFound =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OpcodeNotFound" []
      | CallNotAllowedInsideStatic =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallNotAllowedInsideStatic" []
      | StateChangeDuringStaticCall =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StateChangeDuringStaticCall" []
      | InvalidFEOpcode =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidFEOpcode" []
      | InvalidJump =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidJump" []
      | NotActivated =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NotActivated" []
      | StackUnderflow =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackUnderflow" []
      | StackOverflow =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackOverflow" []
      | OutOfOffset =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfOffset" []
      | CreateCollision =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateCollision" []
      | OverflowPayment =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OverflowPayment" []
      | PrecompileError =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileError" []
      | NonceOverflow =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NonceOverflow" []
      | CreateContractSizeLimit =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractSizeLimit" []
      | CreateContractStartingWithEF =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractStartingWithEF" []
      | CreateInitCodeSizeLimit =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeSizeLimit" []
      | FatalExternalError =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::FatalExternalError" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::instruction_result::InstructionResult").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Stop :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Stop" [] =
    φ Stop.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Stop : of_value.

  Lemma of_value_with_Return :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Return" [] =
    φ Return.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Return : of_value.

  Lemma of_value_with_SelfDestruct :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::SelfDestruct" [] =
    φ SelfDestruct.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_SelfDestruct : of_value.

  Lemma of_value_with_Revert :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Revert" [] =
    φ Revert.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Revert : of_value.

  Lemma of_value_with_CallTooDeep :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallTooDeep" [] =
    φ CallTooDeep.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CallTooDeep : of_value.

  Lemma of_value_with_OutOfFunds :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfFunds" [] =
    φ OutOfFunds.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfFunds : of_value.

  Lemma of_value_with_CreateInitCodeStartingEF00 :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeStartingEF00" [] =
    φ CreateInitCodeStartingEF00.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateInitCodeStartingEF00 : of_value.

  Lemma of_value_with_InvalidEOFInitCode :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidEOFInitCode" [] =
    φ InvalidEOFInitCode.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidEOFInitCode : of_value.

  Lemma of_value_with_InvalidExtDelegateCallTarget :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidExtDelegateCallTarget" [] =
    φ InvalidExtDelegateCallTarget.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidExtDelegateCallTarget : of_value.

  Lemma of_value_with_OutOfGas :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfGas" [] =
    φ OutOfGas.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfGas : of_value.

  Lemma of_value_with_MemoryOOG :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryOOG" [] =
    φ MemoryOOG.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MemoryOOG : of_value.

  Lemma of_value_with_MemoryLimitOOG :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryLimitOOG" [] =
    φ MemoryLimitOOG.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MemoryLimitOOG : of_value.

  Lemma of_value_with_PrecompileOOG :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileOOG" [] =
    φ PrecompileOOG.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PrecompileOOG : of_value.

  Lemma of_value_with_InvalidOperandOOG :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidOperandOOG" [] =
    φ InvalidOperandOOG.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidOperandOOG : of_value.

  Lemma of_value_with_ReentrancySentryOOG :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReentrancySentryOOG" [] =
    φ ReentrancySentryOOG.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ReentrancySentryOOG : of_value.

  Lemma of_value_with_OpcodeNotFound :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OpcodeNotFound" [] =
    φ OpcodeNotFound.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OpcodeNotFound : of_value.

  Lemma of_value_with_CallNotAllowedInsideStatic :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallNotAllowedInsideStatic" [] =
    φ CallNotAllowedInsideStatic.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CallNotAllowedInsideStatic : of_value.

  Lemma of_value_with_StateChangeDuringStaticCall :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StateChangeDuringStaticCall" [] =
    φ StateChangeDuringStaticCall.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StateChangeDuringStaticCall : of_value.

  Lemma of_value_with_InvalidFEOpcode :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidFEOpcode" [] =
    φ InvalidFEOpcode.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidFEOpcode : of_value.

  Lemma of_value_with_InvalidJump :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidJump" [] =
    φ InvalidJump.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidJump : of_value.

  Lemma of_value_with_NotActivated :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NotActivated" [] =
    φ NotActivated.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NotActivated : of_value.

  Lemma of_value_with_StackUnderflow :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackUnderflow" [] =
    φ StackUnderflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StackUnderflow : of_value.

  Lemma of_value_with_StackOverflow :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackOverflow" [] =
    φ StackOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StackOverflow : of_value.

  Lemma of_value_with_OutOfOffset :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfOffset" [] =
    φ OutOfOffset.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfOffset : of_value.

  Lemma of_value_with_CreateCollision :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateCollision" [] =
    φ CreateCollision.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateCollision : of_value.

  Lemma of_value_with_OverflowPayment :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OverflowPayment" [] =
    φ OverflowPayment.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OverflowPayment : of_value.

  Lemma of_value_with_PrecompileError :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileError" [] =
    φ PrecompileError.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PrecompileError : of_value.

  Lemma of_value_with_NonceOverflow :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NonceOverflow" [] =
    φ NonceOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NonceOverflow : of_value.

  Lemma of_value_with_CreateContractSizeLimit :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractSizeLimit" [] =
    φ CreateContractSizeLimit.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateContractSizeLimit : of_value.

  Lemma of_value_with_CreateContractStartingWithEF :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractStartingWithEF" [] =
    φ CreateContractStartingWithEF.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateContractStartingWithEF : of_value.

  Lemma of_value_with_CreateInitCodeSizeLimit :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeSizeLimit" [] =
    φ CreateInitCodeSizeLimit.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateInitCodeSizeLimit : of_value.

  Lemma of_value_with_FatalExternalError :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::FatalExternalError" [] =
    φ FatalExternalError.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_FatalExternalError : of_value.

  Definition of_value_Stop :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Stop" []
    ).
  Proof. econstructor; apply of_value_with_Stop; eassumption. Defined.
  Smpl Add simple apply of_value_Stop : of_value.

  Definition of_value_Return :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Return" []
    ).
  Proof. econstructor; apply of_value_with_Return; eassumption. Defined.
  Smpl Add simple apply of_value_Return : of_value.

  Definition of_value_SelfDestruct :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::SelfDestruct" []
    ).
  Proof. econstructor; apply of_value_with_SelfDestruct; eassumption. Defined.
  Smpl Add simple apply of_value_SelfDestruct : of_value.

  Definition of_value_Revert :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Revert" []
    ).
  Proof. econstructor; apply of_value_with_Revert; eassumption. Defined.
  Smpl Add simple apply of_value_Revert : of_value.

  Definition of_value_CallTooDeep :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallTooDeep" []
    ).
  Proof. econstructor; apply of_value_with_CallTooDeep; eassumption. Defined.
  Smpl Add simple apply of_value_CallTooDeep : of_value.

  Definition of_value_OutOfFunds :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfFunds" []
    ).
  Proof. econstructor; apply of_value_with_OutOfFunds; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfFunds : of_value.

  Definition of_value_CreateInitCodeStartingEF00 :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeStartingEF00" []
    ).
  Proof. econstructor; apply of_value_with_CreateInitCodeStartingEF00; eassumption. Defined.
  Smpl Add simple apply of_value_CreateInitCodeStartingEF00 : of_value.

  Definition of_value_InvalidEOFInitCode :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidEOFInitCode" []
    ).
  Proof. econstructor; apply of_value_with_InvalidEOFInitCode; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidEOFInitCode : of_value.

  Definition of_value_InvalidExtDelegateCallTarget :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidExtDelegateCallTarget" []
    ).
  Proof. econstructor; apply of_value_with_InvalidExtDelegateCallTarget; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidExtDelegateCallTarget : of_value.

  Definition of_value_OutOfGas :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfGas" []
    ).
  Proof. econstructor; apply of_value_with_OutOfGas; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfGas : of_value.

  Definition of_value_MemoryOOG :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryOOG" []
    ).
  Proof. econstructor; apply of_value_with_MemoryOOG; eassumption. Defined.
  Smpl Add simple apply of_value_MemoryOOG : of_value.

  Definition of_value_MemoryLimitOOG :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryLimitOOG" []
    ).
  Proof. econstructor; apply of_value_with_MemoryLimitOOG; eassumption. Defined.
  Smpl Add simple apply of_value_MemoryLimitOOG : of_value.

  Definition of_value_PrecompileOOG :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileOOG" []
    ).
  Proof. econstructor; apply of_value_with_PrecompileOOG; eassumption. Defined.
  Smpl Add simple apply of_value_PrecompileOOG : of_value.

  Definition of_value_InvalidOperandOOG :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidOperandOOG" []
    ).
  Proof. econstructor; apply of_value_with_InvalidOperandOOG; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidOperandOOG : of_value.

  Definition of_value_ReentrancySentryOOG :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReentrancySentryOOG" []
    ).
  Proof. econstructor; apply of_value_with_ReentrancySentryOOG; eassumption. Defined.
  Smpl Add simple apply of_value_ReentrancySentryOOG : of_value.

  Definition of_value_OpcodeNotFound :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OpcodeNotFound" []
    ).
  Proof. econstructor; apply of_value_with_OpcodeNotFound; eassumption. Defined.
  Smpl Add simple apply of_value_OpcodeNotFound : of_value.

  Definition of_value_CallNotAllowedInsideStatic :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallNotAllowedInsideStatic" []
    ).
  Proof. econstructor; apply of_value_with_CallNotAllowedInsideStatic; eassumption. Defined.
  Smpl Add simple apply of_value_CallNotAllowedInsideStatic : of_value.

  Definition of_value_StateChangeDuringStaticCall :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StateChangeDuringStaticCall" []
    ).
  Proof. econstructor; apply of_value_with_StateChangeDuringStaticCall; eassumption. Defined.
  Smpl Add simple apply of_value_StateChangeDuringStaticCall : of_value.

  Definition of_value_InvalidFEOpcode :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidFEOpcode" []
    ).
  Proof. econstructor; apply of_value_with_InvalidFEOpcode; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidFEOpcode : of_value.

  Definition of_value_InvalidJump :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidJump" []
    ).
  Proof. econstructor; apply of_value_with_InvalidJump; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidJump : of_value.

  Definition of_value_NotActivated :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NotActivated" []
    ).
  Proof. econstructor; apply of_value_with_NotActivated; eassumption. Defined.
  Smpl Add simple apply of_value_NotActivated : of_value.

  Definition of_value_StackUnderflow :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackUnderflow" []
    ).
  Proof. econstructor; apply of_value_with_StackUnderflow; eassumption. Defined.
  Smpl Add simple apply of_value_StackUnderflow : of_value.

  Definition of_value_StackOverflow :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackOverflow" []
    ).
  Proof. econstructor; apply of_value_with_StackOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_StackOverflow : of_value.

  Definition of_value_OutOfOffset :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfOffset" []
    ).
  Proof. econstructor; apply of_value_with_OutOfOffset; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfOffset : of_value.

  Definition of_value_CreateCollision :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateCollision" []
    ).
  Proof. econstructor; apply of_value_with_CreateCollision; eassumption. Defined.
  Smpl Add simple apply of_value_CreateCollision : of_value.

  Definition of_value_OverflowPayment :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OverflowPayment" []
    ).
  Proof. econstructor; apply of_value_with_OverflowPayment; eassumption. Defined.
  Smpl Add simple apply of_value_OverflowPayment : of_value.

  Definition of_value_PrecompileError :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileError" []
    ).
  Proof. econstructor; apply of_value_with_PrecompileError; eassumption. Defined.
  Smpl Add simple apply of_value_PrecompileError : of_value.

  Definition of_value_NonceOverflow :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NonceOverflow" []
    ).
  Proof. econstructor; apply of_value_with_NonceOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_NonceOverflow : of_value.

  Definition of_value_CreateContractSizeLimit :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractSizeLimit" []
    ).
  Proof. econstructor; apply of_value_with_CreateContractSizeLimit; eassumption. Defined.
  Smpl Add simple apply of_value_CreateContractSizeLimit : of_value.

  Definition of_value_CreateContractStartingWithEF :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractStartingWithEF" []
    ).
  Proof. econstructor; apply of_value_with_CreateContractStartingWithEF; eassumption. Defined.
  Smpl Add simple apply of_value_CreateContractStartingWithEF : of_value.

  Definition of_value_CreateInitCodeSizeLimit :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeSizeLimit" []
    ).
  Proof. econstructor; apply of_value_with_CreateInitCodeSizeLimit; eassumption. Defined.
  Smpl Add simple apply of_value_CreateInitCodeSizeLimit : of_value.

  Definition of_value_FatalExternalError :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::FatalExternalError" []
    ).
  Proof. econstructor; apply of_value_with_FatalExternalError; eassumption. Defined.
  Smpl Add simple apply of_value_FatalExternalError : of_value.

  Module SubPointer.

  End SubPointer.
End InstructionResult.

Module InternalResult.
  Inductive t : Set :=
  | CreateInitCodeStartingEF00
  | InvalidExtDelegateCallTarget
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::instruction_result::InternalResult";
    φ x :=
      match x with
      | CreateInitCodeStartingEF00 =>
        Value.StructTuple "revm_interpreter::instruction_result::InternalResult::CreateInitCodeStartingEF00" []
      | InvalidExtDelegateCallTarget =>
        Value.StructTuple "revm_interpreter::instruction_result::InternalResult::InvalidExtDelegateCallTarget" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::instruction_result::InternalResult").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_CreateInitCodeStartingEF00 :
    Value.StructTuple "revm_interpreter::instruction_result::InternalResult::CreateInitCodeStartingEF00" [] =
    φ CreateInitCodeStartingEF00.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateInitCodeStartingEF00 : of_value.

  Lemma of_value_with_InvalidExtDelegateCallTarget :
    Value.StructTuple "revm_interpreter::instruction_result::InternalResult::InvalidExtDelegateCallTarget" [] =
    φ InvalidExtDelegateCallTarget.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidExtDelegateCallTarget : of_value.

  Definition of_value_CreateInitCodeStartingEF00 :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InternalResult::CreateInitCodeStartingEF00" []
    ).
  Proof. econstructor; apply of_value_with_CreateInitCodeStartingEF00; eassumption. Defined.
  Smpl Add simple apply of_value_CreateInitCodeStartingEF00 : of_value.

  Definition of_value_InvalidExtDelegateCallTarget :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InternalResult::InvalidExtDelegateCallTarget" []
    ).
  Proof. econstructor; apply of_value_with_InvalidExtDelegateCallTarget; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidExtDelegateCallTarget : of_value.

  Module SubPointer.

  End SubPointer.
End InternalResult.

Module SuccessOrHalt.
  Inductive t (HaltReasonTr: Set) : Set :=
  | Success
    (_ : result.SuccessReason.t)
  | Revert
  | Halt
    (_ : HaltReasonTr)
  | FatalExternalError
  | Internal
    (_ : instruction_result.InternalResult.t)
  .
  Arguments Success Revert Halt FatalExternalError Internal {_}.

  Global Instance IsLink (HaltReasonTr: Set) : Link t HaltReasonTr := {
    Φ := Ty.path "revm_interpreter::instruction_result::SuccessOrHalt";
    φ x :=
      match x with
      | Success γ0 =>
        Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Success" [
          φ γ0
        ]
      | Revert =>
        Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Revert" []
      | Halt γ0 =>
        Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Halt" [
          φ γ0
        ]
      | FatalExternalError =>
        Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::FatalExternalError" []
      | Internal γ0 =>
        Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Internal" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::instruction_result::SuccessOrHalt").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Success
    (γ0 : result.SuccessReason.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Success" [
      γ0
    ] =
    φ (Success γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Success : of_value.

  Lemma of_value_with_Revert :
    Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Revert" [] =
    φ Revert.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Revert : of_value.

  Lemma of_value_with_Halt
    (γ0 : HaltReasonTr) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Halt" [
      γ0
    ] =
    φ (Halt γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Halt : of_value.

  Lemma of_value_with_FatalExternalError :
    Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::FatalExternalError" [] =
    φ FatalExternalError.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_FatalExternalError : of_value.

  Lemma of_value_with_Internal
    (γ0 : instruction_result.InternalResult.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Internal" [
      γ0
    ] =
    φ (Internal γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Internal : of_value.

  Definition of_value_Success
    (γ0 : result.SuccessReason.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Success" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Success; eassumption. Defined.
  Smpl Add simple apply of_value_Success : of_value.

  Definition of_value_Revert :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Revert" []
    ).
  Proof. econstructor; apply of_value_with_Revert; eassumption. Defined.
  Smpl Add simple apply of_value_Revert : of_value.

  Definition of_value_Halt
    (γ0 : HaltReasonTr) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Halt" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Halt; eassumption. Defined.
  Smpl Add simple apply of_value_Halt : of_value.

  Definition of_value_FatalExternalError :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::FatalExternalError" []
    ).
  Proof. econstructor; apply of_value_with_FatalExternalError; eassumption. Defined.
  Smpl Add simple apply of_value_FatalExternalError : of_value.

  Definition of_value_Internal
    (γ0 : instruction_result.InternalResult.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Internal" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Internal; eassumption. Defined.
  Smpl Add simple apply of_value_Internal : of_value.

  Module SubPointer.
    Definition get_Success_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Success" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Success γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : result.SuccessReason.t) :=
        match γ with
        | Success _ => Some (Success γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Success_0_is_valid : SubPointer.Runner.Valid.t get_Success_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Success_0_is_valid : run_sub_pointer.

    Definition get_Halt_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Halt" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Halt γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : HaltReasonTr) :=
        match γ with
        | Halt _ => Some (Halt γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Halt_0_is_valid : SubPointer.Runner.Valid.t get_Halt_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Halt_0_is_valid : run_sub_pointer.

    Definition get_Internal_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Internal" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Internal γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : instruction_result.InternalResult.t) :=
        match γ with
        | Internal _ => Some (Internal γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Internal_0_is_valid : SubPointer.Runner.Valid.t get_Internal_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Internal_0_is_valid : run_sub_pointer.
  End SubPointer.
End SuccessOrHalt.

Module Instruction.
  Record t {W H: Set} : Set := {
    fn_: Function1.t (instruction_context.InstructionContext.t H W) ();
    static_gas: U64.t;
  }.
  Arguments Build_t {_ _}.
  Arguments t : clear implicits.

  Global Instance IsLink {W H: Set} `{Link W} `{Link H} : Link (t W H) := {
    Φ := Ty.path "revm_interpreter::instructions::Instruction";
    φ '(Build_t fn_ static_gas) :=
      Value.StructRecord "revm_interpreter::instructions::Instruction" [
        ("fn_", φ fn_);
        ("static_gas", φ static_gas)
      ]
  }.
End Instruction.

Module Interpreter.
  Record t {WIRE: Set} : Set := {
    bytecode: Unknown type {'AssociatedInTrait': {'trait_name': ['revm_interpreter', 'interpreter_types', 'InterpreterTypes'], 'const_args': [], 'ty_args': [], 'self_ty': {'Var': {'name': 'WIRE'}}, 'name': 'Bytecode'}};
    gas: gas.Gas.t;
    stack: Unknown type {'AssociatedInTrait': {'trait_name': ['revm_interpreter', 'interpreter_types', 'InterpreterTypes'], 'const_args': [], 'ty_args': [], 'self_ty': {'Var': {'name': 'WIRE'}}, 'name': 'Stack'}};
    return_data: Unknown type {'AssociatedInTrait': {'trait_name': ['revm_interpreter', 'interpreter_types', 'InterpreterTypes'], 'const_args': [], 'ty_args': [], 'self_ty': {'Var': {'name': 'WIRE'}}, 'name': 'ReturnData'}};
    memory: Unknown type {'AssociatedInTrait': {'trait_name': ['revm_interpreter', 'interpreter_types', 'InterpreterTypes'], 'const_args': [], 'ty_args': [], 'self_ty': {'Var': {'name': 'WIRE'}}, 'name': 'Memory'}};
    input: Unknown type {'AssociatedInTrait': {'trait_name': ['revm_interpreter', 'interpreter_types', 'InterpreterTypes'], 'const_args': [], 'ty_args': [], 'self_ty': {'Var': {'name': 'WIRE'}}, 'name': 'Input'}};
    runtime_flag: Unknown type {'AssociatedInTrait': {'trait_name': ['revm_interpreter', 'interpreter_types', 'InterpreterTypes'], 'const_args': [], 'ty_args': [], 'self_ty': {'Var': {'name': 'WIRE'}}, 'name': 'RuntimeFlag'}};
    extend: Unknown type {'AssociatedInTrait': {'trait_name': ['revm_interpreter', 'interpreter_types', 'InterpreterTypes'], 'const_args': [], 'ty_args': [], 'self_ty': {'Var': {'name': 'WIRE'}}, 'name': 'Extend'}};
  }.
  Arguments Build_t {_}.
  Arguments t : clear implicits.

  Global Instance IsLink {WIRE: Set} `{Link WIRE} : Link (t WIRE) := {
    Φ := Ty.path "revm_interpreter::interpreter::Interpreter";
    φ '(Build_t bytecode gas stack return_data memory input runtime_flag extend) :=
      Value.StructRecord "revm_interpreter::interpreter::Interpreter" [
        ("bytecode", φ bytecode);
        ("gas", φ gas);
        ("stack", φ stack);
        ("return_data", φ return_data);
        ("memory", φ memory);
        ("input", φ input);
        ("runtime_flag", φ runtime_flag);
        ("extend", φ extend)
      ]
  }.
End Interpreter.

Module EthInterpreter.
  Record t {EXT MG: Set} : Set := {
    _phantom: marker.PhantomData.t (Function0.t (EXT * MG));
  }.
  Arguments Build_t {_ _}.
  Arguments t : clear implicits.

  Global Instance IsLink {EXT MG: Set} `{Link EXT} `{Link MG} : Link (t EXT MG) := {
    Φ := Ty.path "revm_interpreter::interpreter::EthInterpreter";
    φ '(Build_t _phantom) :=
      Value.StructRecord "revm_interpreter::interpreter::EthInterpreter" [
        ("_phantom", φ _phantom)
      ]
  }.
End EthInterpreter.

Module InterpreterResult.
  Record t : Set := {
    result: instruction_result.InstructionResult.t;
    output: bytes_.Bytes.t;
    gas: gas.Gas.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::InterpreterResult";
    φ '(Build_t result output gas) :=
      Value.StructRecord "revm_interpreter::interpreter::InterpreterResult" [
        ("result", φ result);
        ("output", φ output);
        ("gas", φ gas)
      ]
  }.
End InterpreterResult.

Module FrameInput.
  Inductive t : Set :=
  | Empty
  | Call
    (_ : boxed.Box.t call_inputs.CallInputs.t alloc.Global.t)
  | Create
    (_ : boxed.Box.t create_inputs.CreateInputs.t alloc.Global.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::FrameInput";
    φ x :=
      match x with
      | Empty =>
        Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Empty" []
      | Call γ0 =>
        Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Call" [
          φ γ0
        ]
      | Create γ0 =>
        Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Create" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::interpreter_action::FrameInput").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Empty :
    Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Empty" [] =
    φ Empty.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Empty : of_value.

  Lemma of_value_with_Call
    (γ0 : boxed.Box.t call_inputs.CallInputs.t alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Call" [
      γ0
    ] =
    φ (Call γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Call : of_value.

  Lemma of_value_with_Create
    (γ0 : boxed.Box.t create_inputs.CreateInputs.t alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Create" [
      γ0
    ] =
    φ (Create γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Create : of_value.

  Definition of_value_Empty :
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Empty" []
    ).
  Proof. econstructor; apply of_value_with_Empty; eassumption. Defined.
  Smpl Add simple apply of_value_Empty : of_value.

  Definition of_value_Call
    (γ0 : boxed.Box.t call_inputs.CallInputs.t alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Call" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Call; eassumption. Defined.
  Smpl Add simple apply of_value_Call : of_value.

  Definition of_value_Create
    (γ0 : boxed.Box.t create_inputs.CreateInputs.t alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Create" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Create; eassumption. Defined.
  Smpl Add simple apply of_value_Create : of_value.

  Module SubPointer.
    Definition get_Call_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_interpreter::interpreter_action::FrameInput::Call" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Call γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : boxed.Box.t call_inputs.CallInputs.t alloc.Global.t) :=
        match γ with
        | Call _ => Some (Call γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Call_0_is_valid : SubPointer.Runner.Valid.t get_Call_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Call_0_is_valid : run_sub_pointer.

    Definition get_Create_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_interpreter::interpreter_action::FrameInput::Create" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Create γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : boxed.Box.t create_inputs.CreateInputs.t alloc.Global.t) :=
        match γ with
        | Create _ => Some (Create γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Create_0_is_valid : SubPointer.Runner.Valid.t get_Create_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Create_0_is_valid : run_sub_pointer.
  End SubPointer.
End FrameInput.

Module FrameInit.
  Record t : Set := {
    depth: Usize.t;
    memory: shared_memory.SharedMemory.t;
    frame_input: interpreter_action.FrameInput.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::FrameInit";
    φ '(Build_t depth memory frame_input) :=
      Value.StructRecord "revm_interpreter::interpreter_action::FrameInit" [
        ("depth", φ depth);
        ("memory", φ memory);
        ("frame_input", φ frame_input)
      ]
  }.
End FrameInit.

Module InterpreterAction.
  Inductive t : Set :=
  | NewFrame
    (_ : interpreter_action.FrameInput.t)
  | Return
    (_ : interpreter.InterpreterResult.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::InterpreterAction";
    φ x :=
      match x with
      | NewFrame γ0 =>
        Value.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::NewFrame" [
          φ γ0
        ]
      | Return γ0 =>
        Value.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::Return" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::interpreter_action::InterpreterAction").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_NewFrame
    (γ0 : interpreter_action.FrameInput.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::NewFrame" [
      γ0
    ] =
    φ (NewFrame γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NewFrame : of_value.

  Lemma of_value_with_Return
    (γ0 : interpreter.InterpreterResult.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::Return" [
      γ0
    ] =
    φ (Return γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Return : of_value.

  Definition of_value_NewFrame
    (γ0 : interpreter_action.FrameInput.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::NewFrame" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_NewFrame; eassumption. Defined.
  Smpl Add simple apply of_value_NewFrame : of_value.

  Definition of_value_Return
    (γ0 : interpreter.InterpreterResult.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::Return" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Return; eassumption. Defined.
  Smpl Add simple apply of_value_Return : of_value.

  Module SubPointer.
    Definition get_NewFrame_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::NewFrame" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | NewFrame γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : interpreter_action.FrameInput.t) :=
        match γ with
        | NewFrame _ => Some (NewFrame γ_0)
        | _ => None
        end;
    |}.

    Lemma get_NewFrame_0_is_valid : SubPointer.Runner.Valid.t get_NewFrame_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_NewFrame_0_is_valid : run_sub_pointer.

    Definition get_Return_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::Return" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Return γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : interpreter.InterpreterResult.t) :=
        match γ with
        | Return _ => Some (Return γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Return_0_is_valid : SubPointer.Runner.Valid.t get_Return_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Return_0_is_valid : run_sub_pointer.
  End SubPointer.
End InterpreterAction.

Module InitialAndFloorGas.
  Record t : Set := {
    initial_gas: U64.t;
    floor_gas: U64.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::gas::calc::InitialAndFloorGas";
    φ '(Build_t initial_gas floor_gas) :=
      Value.StructRecord "revm_interpreter::gas::calc::InitialAndFloorGas" [
        ("initial_gas", φ initial_gas);
        ("floor_gas", φ floor_gas)
      ]
  }.
End InitialAndFloorGas.

Module Sign.
  Inductive t : Set :=
  | Minus
  | Zero
  | Plus
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::instructions::i256::Sign";
    φ x :=
      match x with
      | Minus =>
        Value.StructTuple "revm_interpreter::instructions::i256::Sign::Minus" []
      | Zero =>
        Value.StructTuple "revm_interpreter::instructions::i256::Sign::Zero" []
      | Plus =>
        Value.StructTuple "revm_interpreter::instructions::i256::Sign::Plus" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::instructions::i256::Sign").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Minus :
    Value.StructTuple "revm_interpreter::instructions::i256::Sign::Minus" [] =
    φ Minus.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Minus : of_value.

  Lemma of_value_with_Zero :
    Value.StructTuple "revm_interpreter::instructions::i256::Sign::Zero" [] =
    φ Zero.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Zero : of_value.

  Lemma of_value_with_Plus :
    Value.StructTuple "revm_interpreter::instructions::i256::Sign::Plus" [] =
    φ Plus.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Plus : of_value.

  Definition of_value_Minus :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instructions::i256::Sign::Minus" []
    ).
  Proof. econstructor; apply of_value_with_Minus; eassumption. Defined.
  Smpl Add simple apply of_value_Minus : of_value.

  Definition of_value_Zero :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instructions::i256::Sign::Zero" []
    ).
  Proof. econstructor; apply of_value_with_Zero; eassumption. Defined.
  Smpl Add simple apply of_value_Zero : of_value.

  Definition of_value_Plus :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instructions::i256::Sign::Plus" []
    ).
  Proof. econstructor; apply of_value_with_Plus; eassumption. Defined.
  Smpl Add simple apply of_value_Plus : of_value.

  Module SubPointer.

  End SubPointer.
End Sign.

Module ExtBytecode.
  Record t : Set := {
    instruction_pointer: '*const U8.t;
    continue_execution: bool;
    bytecode_hash: option.Option.t (fixed.FixedBytes.t 32);
    action: option.Option.t interpreter_action.InterpreterAction.t;
    base: bytecode.Bytecode.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::ext_bytecode::ExtBytecode";
    φ '(Build_t instruction_pointer continue_execution bytecode_hash action base) :=
      Value.StructRecord "revm_interpreter::interpreter::ext_bytecode::ExtBytecode" [
        ("instruction_pointer", φ instruction_pointer);
        ("continue_execution", φ continue_execution);
        ("bytecode_hash", φ bytecode_hash);
        ("action", φ action);
        ("base", φ base)
      ]
  }.
End ExtBytecode.

Module InputsImpl.
  Record t : Set := {
    target_address: address.Address.t;
    bytecode_address: option.Option.t address.Address.t;
    caller_address: address.Address.t;
    input: call_inputs.CallInput.t;
    call_value: ruint.Uint.t 256 4;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::input::InputsImpl";
    φ '(Build_t target_address bytecode_address caller_address input call_value) :=
      Value.StructRecord "revm_interpreter::interpreter::input::InputsImpl" [
        ("target_address", φ target_address);
        ("bytecode_address", φ bytecode_address);
        ("caller_address", φ caller_address);
        ("input", φ input);
        ("call_value", φ call_value)
      ]
  }.
End InputsImpl.

Module RuntimeFlags.
  Record t : Set := {
    is_static: bool;
    spec_id: hardfork.SpecId.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::runtime_flags::RuntimeFlags";
    φ '(Build_t is_static spec_id) :=
      Value.StructRecord "revm_interpreter::interpreter::runtime_flags::RuntimeFlags" [
        ("is_static", φ is_static);
        ("spec_id", φ spec_id)
      ]
  }.
End RuntimeFlags.

Module SharedMemory.
  Record t : Set := {
    buffer: option.Option.t (rc.Rc.t (cell.RefCell.t (vec.Vec.t U8.t alloc.Global.t)) alloc.Global.t);
    my_checkpoint: Usize.t;
    child_checkpoint: option.Option.t Usize.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::shared_memory::SharedMemory";
    φ '(Build_t buffer my_checkpoint child_checkpoint) :=
      Value.StructRecord "revm_interpreter::interpreter::shared_memory::SharedMemory" [
        ("buffer", φ buffer);
        ("my_checkpoint", φ my_checkpoint);
        ("child_checkpoint", φ child_checkpoint)
      ]
  }.
End SharedMemory.

Module Stack.
  Record t : Set := {
    data: vec.Vec.t (ruint.Uint.t 256 4) alloc.Global.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::stack::Stack";
    φ '(Build_t data) :=
      Value.StructRecord "revm_interpreter::interpreter::stack::Stack" [
        ("data", φ data)
      ]
  }.
End Stack.

Module CallInput.
  Inductive t : Set :=
  | SharedBuffer
    (_ : range.Range.t Usize.t)
  | Bytes
    (_ : bytes_.Bytes.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::call_inputs::CallInput";
    φ x :=
      match x with
      | SharedBuffer γ0 =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallInput::SharedBuffer" [
          φ γ0
        ]
      | Bytes γ0 =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallInput::Bytes" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::interpreter_action::call_inputs::CallInput").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_SharedBuffer
    (γ0 : range.Range.t Usize.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallInput::SharedBuffer" [
      γ0
    ] =
    φ (SharedBuffer γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_SharedBuffer : of_value.

  Lemma of_value_with_Bytes
    (γ0 : bytes_.Bytes.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallInput::Bytes" [
      γ0
    ] =
    φ (Bytes γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bytes : of_value.

  Definition of_value_SharedBuffer
    (γ0 : range.Range.t Usize.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallInput::SharedBuffer" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_SharedBuffer; eassumption. Defined.
  Smpl Add simple apply of_value_SharedBuffer : of_value.

  Definition of_value_Bytes
    (γ0 : bytes_.Bytes.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallInput::Bytes" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Bytes; eassumption. Defined.
  Smpl Add simple apply of_value_Bytes : of_value.

  Module SubPointer.
    Definition get_SharedBuffer_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallInput::SharedBuffer" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | SharedBuffer γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : range.Range.t Usize.t) :=
        match γ with
        | SharedBuffer _ => Some (SharedBuffer γ_0)
        | _ => None
        end;
    |}.

    Lemma get_SharedBuffer_0_is_valid : SubPointer.Runner.Valid.t get_SharedBuffer_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_SharedBuffer_0_is_valid : run_sub_pointer.

    Definition get_Bytes_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallInput::Bytes" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Bytes γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : bytes_.Bytes.t) :=
        match γ with
        | Bytes _ => Some (Bytes γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Bytes_0_is_valid : SubPointer.Runner.Valid.t get_Bytes_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Bytes_0_is_valid : run_sub_pointer.
  End SubPointer.
End CallInput.

Module CallInputs.
  Record t : Set := {
    input: call_inputs.CallInput.t;
    return_memory_offset: range.Range.t Usize.t;
    gas_limit: U64.t;
    bytecode_address: address.Address.t;
    known_bytecode: option.Option.t ((fixed.FixedBytes.t 32) * bytecode.Bytecode.t);
    target_address: address.Address.t;
    caller: address.Address.t;
    value: call_inputs.CallValue.t;
    scheme: call_inputs.CallScheme.t;
    is_static: bool;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::call_inputs::CallInputs";
    φ '(Build_t input return_memory_offset gas_limit bytecode_address known_bytecode target_address caller value scheme is_static) :=
      Value.StructRecord "revm_interpreter::interpreter_action::call_inputs::CallInputs" [
        ("input", φ input);
        ("return_memory_offset", φ return_memory_offset);
        ("gas_limit", φ gas_limit);
        ("bytecode_address", φ bytecode_address);
        ("known_bytecode", φ known_bytecode);
        ("target_address", φ target_address);
        ("caller", φ caller);
        ("value", φ value);
        ("scheme", φ scheme);
        ("is_static", φ is_static)
      ]
  }.
End CallInputs.

Module CallScheme.
  Inductive t : Set :=
  | Call
  | CallCode
  | DelegateCall
  | StaticCall
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::call_inputs::CallScheme";
    φ x :=
      match x with
      | Call =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::Call" []
      | CallCode =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::CallCode" []
      | DelegateCall =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::DelegateCall" []
      | StaticCall =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::StaticCall" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::interpreter_action::call_inputs::CallScheme").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Call :
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::Call" [] =
    φ Call.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Call : of_value.

  Lemma of_value_with_CallCode :
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::CallCode" [] =
    φ CallCode.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CallCode : of_value.

  Lemma of_value_with_DelegateCall :
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::DelegateCall" [] =
    φ DelegateCall.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_DelegateCall : of_value.

  Lemma of_value_with_StaticCall :
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::StaticCall" [] =
    φ StaticCall.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StaticCall : of_value.

  Definition of_value_Call :
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::Call" []
    ).
  Proof. econstructor; apply of_value_with_Call; eassumption. Defined.
  Smpl Add simple apply of_value_Call : of_value.

  Definition of_value_CallCode :
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::CallCode" []
    ).
  Proof. econstructor; apply of_value_with_CallCode; eassumption. Defined.
  Smpl Add simple apply of_value_CallCode : of_value.

  Definition of_value_DelegateCall :
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::DelegateCall" []
    ).
  Proof. econstructor; apply of_value_with_DelegateCall; eassumption. Defined.
  Smpl Add simple apply of_value_DelegateCall : of_value.

  Definition of_value_StaticCall :
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::StaticCall" []
    ).
  Proof. econstructor; apply of_value_with_StaticCall; eassumption. Defined.
  Smpl Add simple apply of_value_StaticCall : of_value.

  Module SubPointer.

  End SubPointer.
End CallScheme.

Module CallValue.
  Inductive t : Set :=
  | Transfer
    (_ : ruint.Uint.t 256 4)
  | Apparent
    (_ : ruint.Uint.t 256 4)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::call_inputs::CallValue";
    φ x :=
      match x with
      | Transfer γ0 =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Transfer" [
          φ γ0
        ]
      | Apparent γ0 =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Apparent" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::interpreter_action::call_inputs::CallValue").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Transfer
    (γ0 : ruint.Uint.t 256 4) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Transfer" [
      γ0
    ] =
    φ (Transfer γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Transfer : of_value.

  Lemma of_value_with_Apparent
    (γ0 : ruint.Uint.t 256 4) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Apparent" [
      γ0
    ] =
    φ (Apparent γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Apparent : of_value.

  Definition of_value_Transfer
    (γ0 : ruint.Uint.t 256 4) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Transfer" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Transfer; eassumption. Defined.
  Smpl Add simple apply of_value_Transfer : of_value.

  Definition of_value_Apparent
    (γ0 : ruint.Uint.t 256 4) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Apparent" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Apparent; eassumption. Defined.
  Smpl Add simple apply of_value_Apparent : of_value.

  Module SubPointer.
    Definition get_Transfer_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Transfer" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Transfer γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : ruint.Uint.t 256 4) :=
        match γ with
        | Transfer _ => Some (Transfer γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Transfer_0_is_valid : SubPointer.Runner.Valid.t get_Transfer_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Transfer_0_is_valid : run_sub_pointer.

    Definition get_Apparent_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Apparent" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Apparent γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : ruint.Uint.t 256 4) :=
        match γ with
        | Apparent _ => Some (Apparent γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Apparent_0_is_valid : SubPointer.Runner.Valid.t get_Apparent_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Apparent_0_is_valid : run_sub_pointer.
  End SubPointer.
End CallValue.

Module CallOutcome.
  Record t : Set := {
    result: interpreter.InterpreterResult.t;
    memory_offset: range.Range.t Usize.t;
    was_precompile_called: bool;
    precompile_call_logs: vec.Vec.t (log.Log.t log.LogData.t) alloc.Global.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::call_outcome::CallOutcome";
    φ '(Build_t result memory_offset was_precompile_called precompile_call_logs) :=
      Value.StructRecord "revm_interpreter::interpreter_action::call_outcome::CallOutcome" [
        ("result", φ result);
        ("memory_offset", φ memory_offset);
        ("was_precompile_called", φ was_precompile_called);
        ("precompile_call_logs", φ precompile_call_logs)
      ]
  }.
End CallOutcome.

Module CreateInputs.
  Record t : Set := {
    caller: address.Address.t;
    scheme: cfg.CreateScheme.t;
    value: ruint.Uint.t 256 4;
    init_code: bytes_.Bytes.t;
    gas_limit: U64.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::create_inputs::CreateInputs";
    φ '(Build_t caller scheme value init_code gas_limit) :=
      Value.StructRecord "revm_interpreter::interpreter_action::create_inputs::CreateInputs" [
        ("caller", φ caller);
        ("scheme", φ scheme);
        ("value", φ value);
        ("init_code", φ init_code);
        ("gas_limit", φ gas_limit)
      ]
  }.
End CreateInputs.

Module CreateOutcome.
  Record t : Set := {
    result: interpreter.InterpreterResult.t;
    address: option.Option.t address.Address.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::create_outcome::CreateOutcome";
    φ '(Build_t result address) :=
      Value.StructRecord "revm_interpreter::interpreter_action::create_outcome::CreateOutcome" [
        ("result", φ result);
        ("address", φ address)
      ]
  }.
End CreateOutcome.

Module PrecompileId.
  Inductive t : Set :=
  | EcRec
  | Sha256
  | Ripemd160
  | Identity
  | ModExp
  | Bn254Add
  | Bn254Mul
  | Bn254Pairing
  | Blake2F
  | KzgPointEvaluation
  | Bls12G1Add
  | Bls12G1Msm
  | Bls12G2Add
  | Bls12G2Msm
  | Bls12Pairing
  | Bls12MapFpToGp1
  | Bls12MapFp2ToGp2
  | P256Verify
  | Custom
    (_ : borrow.Cow.t str.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_precompile::id::PrecompileId";
    φ x :=
      match x with
      | EcRec =>
        Value.StructTuple "revm_precompile::id::PrecompileId::EcRec" []
      | Sha256 =>
        Value.StructTuple "revm_precompile::id::PrecompileId::Sha256" []
      | Ripemd160 =>
        Value.StructTuple "revm_precompile::id::PrecompileId::Ripemd160" []
      | Identity =>
        Value.StructTuple "revm_precompile::id::PrecompileId::Identity" []
      | ModExp =>
        Value.StructTuple "revm_precompile::id::PrecompileId::ModExp" []
      | Bn254Add =>
        Value.StructTuple "revm_precompile::id::PrecompileId::Bn254Add" []
      | Bn254Mul =>
        Value.StructTuple "revm_precompile::id::PrecompileId::Bn254Mul" []
      | Bn254Pairing =>
        Value.StructTuple "revm_precompile::id::PrecompileId::Bn254Pairing" []
      | Blake2F =>
        Value.StructTuple "revm_precompile::id::PrecompileId::Blake2F" []
      | KzgPointEvaluation =>
        Value.StructTuple "revm_precompile::id::PrecompileId::KzgPointEvaluation" []
      | Bls12G1Add =>
        Value.StructTuple "revm_precompile::id::PrecompileId::Bls12G1Add" []
      | Bls12G1Msm =>
        Value.StructTuple "revm_precompile::id::PrecompileId::Bls12G1Msm" []
      | Bls12G2Add =>
        Value.StructTuple "revm_precompile::id::PrecompileId::Bls12G2Add" []
      | Bls12G2Msm =>
        Value.StructTuple "revm_precompile::id::PrecompileId::Bls12G2Msm" []
      | Bls12Pairing =>
        Value.StructTuple "revm_precompile::id::PrecompileId::Bls12Pairing" []
      | Bls12MapFpToGp1 =>
        Value.StructTuple "revm_precompile::id::PrecompileId::Bls12MapFpToGp1" []
      | Bls12MapFp2ToGp2 =>
        Value.StructTuple "revm_precompile::id::PrecompileId::Bls12MapFp2ToGp2" []
      | P256Verify =>
        Value.StructTuple "revm_precompile::id::PrecompileId::P256Verify" []
      | Custom γ0 =>
        Value.StructTuple "revm_precompile::id::PrecompileId::Custom" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_precompile::id::PrecompileId").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_EcRec :
    Value.StructTuple "revm_precompile::id::PrecompileId::EcRec" [] =
    φ EcRec.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_EcRec : of_value.

  Lemma of_value_with_Sha256 :
    Value.StructTuple "revm_precompile::id::PrecompileId::Sha256" [] =
    φ Sha256.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Sha256 : of_value.

  Lemma of_value_with_Ripemd160 :
    Value.StructTuple "revm_precompile::id::PrecompileId::Ripemd160" [] =
    φ Ripemd160.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Ripemd160 : of_value.

  Lemma of_value_with_Identity :
    Value.StructTuple "revm_precompile::id::PrecompileId::Identity" [] =
    φ Identity.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Identity : of_value.

  Lemma of_value_with_ModExp :
    Value.StructTuple "revm_precompile::id::PrecompileId::ModExp" [] =
    φ ModExp.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ModExp : of_value.

  Lemma of_value_with_Bn254Add :
    Value.StructTuple "revm_precompile::id::PrecompileId::Bn254Add" [] =
    φ Bn254Add.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bn254Add : of_value.

  Lemma of_value_with_Bn254Mul :
    Value.StructTuple "revm_precompile::id::PrecompileId::Bn254Mul" [] =
    φ Bn254Mul.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bn254Mul : of_value.

  Lemma of_value_with_Bn254Pairing :
    Value.StructTuple "revm_precompile::id::PrecompileId::Bn254Pairing" [] =
    φ Bn254Pairing.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bn254Pairing : of_value.

  Lemma of_value_with_Blake2F :
    Value.StructTuple "revm_precompile::id::PrecompileId::Blake2F" [] =
    φ Blake2F.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Blake2F : of_value.

  Lemma of_value_with_KzgPointEvaluation :
    Value.StructTuple "revm_precompile::id::PrecompileId::KzgPointEvaluation" [] =
    φ KzgPointEvaluation.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_KzgPointEvaluation : of_value.

  Lemma of_value_with_Bls12G1Add :
    Value.StructTuple "revm_precompile::id::PrecompileId::Bls12G1Add" [] =
    φ Bls12G1Add.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12G1Add : of_value.

  Lemma of_value_with_Bls12G1Msm :
    Value.StructTuple "revm_precompile::id::PrecompileId::Bls12G1Msm" [] =
    φ Bls12G1Msm.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12G1Msm : of_value.

  Lemma of_value_with_Bls12G2Add :
    Value.StructTuple "revm_precompile::id::PrecompileId::Bls12G2Add" [] =
    φ Bls12G2Add.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12G2Add : of_value.

  Lemma of_value_with_Bls12G2Msm :
    Value.StructTuple "revm_precompile::id::PrecompileId::Bls12G2Msm" [] =
    φ Bls12G2Msm.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12G2Msm : of_value.

  Lemma of_value_with_Bls12Pairing :
    Value.StructTuple "revm_precompile::id::PrecompileId::Bls12Pairing" [] =
    φ Bls12Pairing.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12Pairing : of_value.

  Lemma of_value_with_Bls12MapFpToGp1 :
    Value.StructTuple "revm_precompile::id::PrecompileId::Bls12MapFpToGp1" [] =
    φ Bls12MapFpToGp1.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12MapFpToGp1 : of_value.

  Lemma of_value_with_Bls12MapFp2ToGp2 :
    Value.StructTuple "revm_precompile::id::PrecompileId::Bls12MapFp2ToGp2" [] =
    φ Bls12MapFp2ToGp2.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12MapFp2ToGp2 : of_value.

  Lemma of_value_with_P256Verify :
    Value.StructTuple "revm_precompile::id::PrecompileId::P256Verify" [] =
    φ P256Verify.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_P256Verify : of_value.

  Lemma of_value_with_Custom
    (γ0 : borrow.Cow.t str.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_precompile::id::PrecompileId::Custom" [
      γ0
    ] =
    φ (Custom γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Custom : of_value.

  Definition of_value_EcRec :
    OfValue.t (
      Value.StructTuple "revm_precompile::id::PrecompileId::EcRec" []
    ).
  Proof. econstructor; apply of_value_with_EcRec; eassumption. Defined.
  Smpl Add simple apply of_value_EcRec : of_value.

  Definition of_value_Sha256 :
    OfValue.t (
      Value.StructTuple "revm_precompile::id::PrecompileId::Sha256" []
    ).
  Proof. econstructor; apply of_value_with_Sha256; eassumption. Defined.
  Smpl Add simple apply of_value_Sha256 : of_value.

  Definition of_value_Ripemd160 :
    OfValue.t (
      Value.StructTuple "revm_precompile::id::PrecompileId::Ripemd160" []
    ).
  Proof. econstructor; apply of_value_with_Ripemd160; eassumption. Defined.
  Smpl Add simple apply of_value_Ripemd160 : of_value.

  Definition of_value_Identity :
    OfValue.t (
      Value.StructTuple "revm_precompile::id::PrecompileId::Identity" []
    ).
  Proof. econstructor; apply of_value_with_Identity; eassumption. Defined.
  Smpl Add simple apply of_value_Identity : of_value.

  Definition of_value_ModExp :
    OfValue.t (
      Value.StructTuple "revm_precompile::id::PrecompileId::ModExp" []
    ).
  Proof. econstructor; apply of_value_with_ModExp; eassumption. Defined.
  Smpl Add simple apply of_value_ModExp : of_value.

  Definition of_value_Bn254Add :
    OfValue.t (
      Value.StructTuple "revm_precompile::id::PrecompileId::Bn254Add" []
    ).
  Proof. econstructor; apply of_value_with_Bn254Add; eassumption. Defined.
  Smpl Add simple apply of_value_Bn254Add : of_value.

  Definition of_value_Bn254Mul :
    OfValue.t (
      Value.StructTuple "revm_precompile::id::PrecompileId::Bn254Mul" []
    ).
  Proof. econstructor; apply of_value_with_Bn254Mul; eassumption. Defined.
  Smpl Add simple apply of_value_Bn254Mul : of_value.

  Definition of_value_Bn254Pairing :
    OfValue.t (
      Value.StructTuple "revm_precompile::id::PrecompileId::Bn254Pairing" []
    ).
  Proof. econstructor; apply of_value_with_Bn254Pairing; eassumption. Defined.
  Smpl Add simple apply of_value_Bn254Pairing : of_value.

  Definition of_value_Blake2F :
    OfValue.t (
      Value.StructTuple "revm_precompile::id::PrecompileId::Blake2F" []
    ).
  Proof. econstructor; apply of_value_with_Blake2F; eassumption. Defined.
  Smpl Add simple apply of_value_Blake2F : of_value.

  Definition of_value_KzgPointEvaluation :
    OfValue.t (
      Value.StructTuple "revm_precompile::id::PrecompileId::KzgPointEvaluation" []
    ).
  Proof. econstructor; apply of_value_with_KzgPointEvaluation; eassumption. Defined.
  Smpl Add simple apply of_value_KzgPointEvaluation : of_value.

  Definition of_value_Bls12G1Add :
    OfValue.t (
      Value.StructTuple "revm_precompile::id::PrecompileId::Bls12G1Add" []
    ).
  Proof. econstructor; apply of_value_with_Bls12G1Add; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12G1Add : of_value.

  Definition of_value_Bls12G1Msm :
    OfValue.t (
      Value.StructTuple "revm_precompile::id::PrecompileId::Bls12G1Msm" []
    ).
  Proof. econstructor; apply of_value_with_Bls12G1Msm; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12G1Msm : of_value.

  Definition of_value_Bls12G2Add :
    OfValue.t (
      Value.StructTuple "revm_precompile::id::PrecompileId::Bls12G2Add" []
    ).
  Proof. econstructor; apply of_value_with_Bls12G2Add; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12G2Add : of_value.

  Definition of_value_Bls12G2Msm :
    OfValue.t (
      Value.StructTuple "revm_precompile::id::PrecompileId::Bls12G2Msm" []
    ).
  Proof. econstructor; apply of_value_with_Bls12G2Msm; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12G2Msm : of_value.

  Definition of_value_Bls12Pairing :
    OfValue.t (
      Value.StructTuple "revm_precompile::id::PrecompileId::Bls12Pairing" []
    ).
  Proof. econstructor; apply of_value_with_Bls12Pairing; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12Pairing : of_value.

  Definition of_value_Bls12MapFpToGp1 :
    OfValue.t (
      Value.StructTuple "revm_precompile::id::PrecompileId::Bls12MapFpToGp1" []
    ).
  Proof. econstructor; apply of_value_with_Bls12MapFpToGp1; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12MapFpToGp1 : of_value.

  Definition of_value_Bls12MapFp2ToGp2 :
    OfValue.t (
      Value.StructTuple "revm_precompile::id::PrecompileId::Bls12MapFp2ToGp2" []
    ).
  Proof. econstructor; apply of_value_with_Bls12MapFp2ToGp2; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12MapFp2ToGp2 : of_value.

  Definition of_value_P256Verify :
    OfValue.t (
      Value.StructTuple "revm_precompile::id::PrecompileId::P256Verify" []
    ).
  Proof. econstructor; apply of_value_with_P256Verify; eassumption. Defined.
  Smpl Add simple apply of_value_P256Verify : of_value.

  Definition of_value_Custom
    (γ0 : borrow.Cow.t str.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_precompile::id::PrecompileId::Custom" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Custom; eassumption. Defined.
  Smpl Add simple apply of_value_Custom : of_value.

  Module SubPointer.
    Definition get_Custom_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_precompile::id::PrecompileId::Custom" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Custom γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : borrow.Cow.t str.t) :=
        match γ with
        | Custom _ => Some (Custom γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Custom_0_is_valid : SubPointer.Runner.Valid.t get_Custom_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Custom_0_is_valid : run_sub_pointer.
  End SubPointer.
End PrecompileId.

Module PrecompileOutput.
  Record t : Set := {
    gas_used: U64.t;
    gas_refunded: I64.t;
    bytes: bytes_.Bytes.t;
    reverted: bool;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_precompile::interface::PrecompileOutput";
    φ '(Build_t gas_used gas_refunded bytes reverted) :=
      Value.StructRecord "revm_precompile::interface::PrecompileOutput" [
        ("gas_used", φ gas_used);
        ("gas_refunded", φ gas_refunded);
        ("bytes", φ bytes);
        ("reverted", φ reverted)
      ]
  }.
End PrecompileOutput.

Module PrecompileError.
  Inductive t : Set :=
  | OutOfGas
  | Blake2WrongLength
  | Blake2WrongFinalIndicatorFlag
  | ModexpExpOverflow
  | ModexpBaseOverflow
  | ModexpModOverflow
  | ModexpEip7823LimitSize
  | Bn254FieldPointNotAMember
  | Bn254AffineGFailedToCreate
  | Bn254PairLength
  | BlobInvalidInputLength
  | BlobMismatchedVersion
  | BlobVerifyKzgProofFailed
  | NonCanonicalFp
  | Bls12381G1NotOnCurve
  | Bls12381G1NotInSubgroup
  | Bls12381G2NotOnCurve
  | Bls12381G2NotInSubgroup
  | Bls12381ScalarInputLength
  | Bls12381G1AddInputLength
  | Bls12381G1MsmInputLength
  | Bls12381G2AddInputLength
  | Bls12381G2MsmInputLength
  | Bls12381PairingInputLength
  | Bls12381MapFpToG1InputLength
  | Bls12381MapFp2ToG2InputLength
  | Bls12381FpPaddingInvalid
  | Bls12381FpPaddingLength
  | Bls12381G1PaddingLength
  | Bls12381G2PaddingLength
  | KzgInvalidG1Point
  | KzgG1PointNotOnCurve
  | KzgG1PointNotInSubgroup
  | KzgInvalidInputLength
  | Secp256k1RecoverFailed
  | Fatal
    (_ : string.String.t)
  | Other
    (_ : borrow.Cow.t str.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_precompile::interface::PrecompileError";
    φ x :=
      match x with
      | OutOfGas =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::OutOfGas" []
      | Blake2WrongLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Blake2WrongLength" []
      | Blake2WrongFinalIndicatorFlag =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Blake2WrongFinalIndicatorFlag" []
      | ModexpExpOverflow =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpExpOverflow" []
      | ModexpBaseOverflow =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpBaseOverflow" []
      | ModexpModOverflow =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpModOverflow" []
      | ModexpEip7823LimitSize =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpEip7823LimitSize" []
      | Bn254FieldPointNotAMember =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bn254FieldPointNotAMember" []
      | Bn254AffineGFailedToCreate =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bn254AffineGFailedToCreate" []
      | Bn254PairLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bn254PairLength" []
      | BlobInvalidInputLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::BlobInvalidInputLength" []
      | BlobMismatchedVersion =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::BlobMismatchedVersion" []
      | BlobVerifyKzgProofFailed =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::BlobVerifyKzgProofFailed" []
      | NonCanonicalFp =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::NonCanonicalFp" []
      | Bls12381G1NotOnCurve =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G1NotOnCurve" []
      | Bls12381G1NotInSubgroup =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G1NotInSubgroup" []
      | Bls12381G2NotOnCurve =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G2NotOnCurve" []
      | Bls12381G2NotInSubgroup =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G2NotInSubgroup" []
      | Bls12381ScalarInputLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381ScalarInputLength" []
      | Bls12381G1AddInputLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G1AddInputLength" []
      | Bls12381G1MsmInputLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G1MsmInputLength" []
      | Bls12381G2AddInputLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G2AddInputLength" []
      | Bls12381G2MsmInputLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G2MsmInputLength" []
      | Bls12381PairingInputLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381PairingInputLength" []
      | Bls12381MapFpToG1InputLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381MapFpToG1InputLength" []
      | Bls12381MapFp2ToG2InputLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381MapFp2ToG2InputLength" []
      | Bls12381FpPaddingInvalid =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381FpPaddingInvalid" []
      | Bls12381FpPaddingLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381FpPaddingLength" []
      | Bls12381G1PaddingLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G1PaddingLength" []
      | Bls12381G2PaddingLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G2PaddingLength" []
      | KzgInvalidG1Point =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::KzgInvalidG1Point" []
      | KzgG1PointNotOnCurve =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::KzgG1PointNotOnCurve" []
      | KzgG1PointNotInSubgroup =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::KzgG1PointNotInSubgroup" []
      | KzgInvalidInputLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::KzgInvalidInputLength" []
      | Secp256k1RecoverFailed =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Secp256k1RecoverFailed" []
      | Fatal γ0 =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Fatal" [
          φ γ0
        ]
      | Other γ0 =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Other" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_precompile::interface::PrecompileError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_OutOfGas :
    Value.StructTuple "revm_precompile::interface::PrecompileError::OutOfGas" [] =
    φ OutOfGas.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfGas : of_value.

  Lemma of_value_with_Blake2WrongLength :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Blake2WrongLength" [] =
    φ Blake2WrongLength.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Blake2WrongLength : of_value.

  Lemma of_value_with_Blake2WrongFinalIndicatorFlag :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Blake2WrongFinalIndicatorFlag" [] =
    φ Blake2WrongFinalIndicatorFlag.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Blake2WrongFinalIndicatorFlag : of_value.

  Lemma of_value_with_ModexpExpOverflow :
    Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpExpOverflow" [] =
    φ ModexpExpOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ModexpExpOverflow : of_value.

  Lemma of_value_with_ModexpBaseOverflow :
    Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpBaseOverflow" [] =
    φ ModexpBaseOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ModexpBaseOverflow : of_value.

  Lemma of_value_with_ModexpModOverflow :
    Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpModOverflow" [] =
    φ ModexpModOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ModexpModOverflow : of_value.

  Lemma of_value_with_ModexpEip7823LimitSize :
    Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpEip7823LimitSize" [] =
    φ ModexpEip7823LimitSize.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ModexpEip7823LimitSize : of_value.

  Lemma of_value_with_Bn254FieldPointNotAMember :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bn254FieldPointNotAMember" [] =
    φ Bn254FieldPointNotAMember.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bn254FieldPointNotAMember : of_value.

  Lemma of_value_with_Bn254AffineGFailedToCreate :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bn254AffineGFailedToCreate" [] =
    φ Bn254AffineGFailedToCreate.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bn254AffineGFailedToCreate : of_value.

  Lemma of_value_with_Bn254PairLength :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bn254PairLength" [] =
    φ Bn254PairLength.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bn254PairLength : of_value.

  Lemma of_value_with_BlobInvalidInputLength :
    Value.StructTuple "revm_precompile::interface::PrecompileError::BlobInvalidInputLength" [] =
    φ BlobInvalidInputLength.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BlobInvalidInputLength : of_value.

  Lemma of_value_with_BlobMismatchedVersion :
    Value.StructTuple "revm_precompile::interface::PrecompileError::BlobMismatchedVersion" [] =
    φ BlobMismatchedVersion.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BlobMismatchedVersion : of_value.

  Lemma of_value_with_BlobVerifyKzgProofFailed :
    Value.StructTuple "revm_precompile::interface::PrecompileError::BlobVerifyKzgProofFailed" [] =
    φ BlobVerifyKzgProofFailed.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BlobVerifyKzgProofFailed : of_value.

  Lemma of_value_with_NonCanonicalFp :
    Value.StructTuple "revm_precompile::interface::PrecompileError::NonCanonicalFp" [] =
    φ NonCanonicalFp.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NonCanonicalFp : of_value.

  Lemma of_value_with_Bls12381G1NotOnCurve :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G1NotOnCurve" [] =
    φ Bls12381G1NotOnCurve.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12381G1NotOnCurve : of_value.

  Lemma of_value_with_Bls12381G1NotInSubgroup :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G1NotInSubgroup" [] =
    φ Bls12381G1NotInSubgroup.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12381G1NotInSubgroup : of_value.

  Lemma of_value_with_Bls12381G2NotOnCurve :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G2NotOnCurve" [] =
    φ Bls12381G2NotOnCurve.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12381G2NotOnCurve : of_value.

  Lemma of_value_with_Bls12381G2NotInSubgroup :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G2NotInSubgroup" [] =
    φ Bls12381G2NotInSubgroup.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12381G2NotInSubgroup : of_value.

  Lemma of_value_with_Bls12381ScalarInputLength :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381ScalarInputLength" [] =
    φ Bls12381ScalarInputLength.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12381ScalarInputLength : of_value.

  Lemma of_value_with_Bls12381G1AddInputLength :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G1AddInputLength" [] =
    φ Bls12381G1AddInputLength.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12381G1AddInputLength : of_value.

  Lemma of_value_with_Bls12381G1MsmInputLength :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G1MsmInputLength" [] =
    φ Bls12381G1MsmInputLength.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12381G1MsmInputLength : of_value.

  Lemma of_value_with_Bls12381G2AddInputLength :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G2AddInputLength" [] =
    φ Bls12381G2AddInputLength.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12381G2AddInputLength : of_value.

  Lemma of_value_with_Bls12381G2MsmInputLength :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G2MsmInputLength" [] =
    φ Bls12381G2MsmInputLength.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12381G2MsmInputLength : of_value.

  Lemma of_value_with_Bls12381PairingInputLength :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381PairingInputLength" [] =
    φ Bls12381PairingInputLength.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12381PairingInputLength : of_value.

  Lemma of_value_with_Bls12381MapFpToG1InputLength :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381MapFpToG1InputLength" [] =
    φ Bls12381MapFpToG1InputLength.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12381MapFpToG1InputLength : of_value.

  Lemma of_value_with_Bls12381MapFp2ToG2InputLength :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381MapFp2ToG2InputLength" [] =
    φ Bls12381MapFp2ToG2InputLength.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12381MapFp2ToG2InputLength : of_value.

  Lemma of_value_with_Bls12381FpPaddingInvalid :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381FpPaddingInvalid" [] =
    φ Bls12381FpPaddingInvalid.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12381FpPaddingInvalid : of_value.

  Lemma of_value_with_Bls12381FpPaddingLength :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381FpPaddingLength" [] =
    φ Bls12381FpPaddingLength.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12381FpPaddingLength : of_value.

  Lemma of_value_with_Bls12381G1PaddingLength :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G1PaddingLength" [] =
    φ Bls12381G1PaddingLength.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12381G1PaddingLength : of_value.

  Lemma of_value_with_Bls12381G2PaddingLength :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G2PaddingLength" [] =
    φ Bls12381G2PaddingLength.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bls12381G2PaddingLength : of_value.

  Lemma of_value_with_KzgInvalidG1Point :
    Value.StructTuple "revm_precompile::interface::PrecompileError::KzgInvalidG1Point" [] =
    φ KzgInvalidG1Point.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_KzgInvalidG1Point : of_value.

  Lemma of_value_with_KzgG1PointNotOnCurve :
    Value.StructTuple "revm_precompile::interface::PrecompileError::KzgG1PointNotOnCurve" [] =
    φ KzgG1PointNotOnCurve.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_KzgG1PointNotOnCurve : of_value.

  Lemma of_value_with_KzgG1PointNotInSubgroup :
    Value.StructTuple "revm_precompile::interface::PrecompileError::KzgG1PointNotInSubgroup" [] =
    φ KzgG1PointNotInSubgroup.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_KzgG1PointNotInSubgroup : of_value.

  Lemma of_value_with_KzgInvalidInputLength :
    Value.StructTuple "revm_precompile::interface::PrecompileError::KzgInvalidInputLength" [] =
    φ KzgInvalidInputLength.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_KzgInvalidInputLength : of_value.

  Lemma of_value_with_Secp256k1RecoverFailed :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Secp256k1RecoverFailed" [] =
    φ Secp256k1RecoverFailed.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Secp256k1RecoverFailed : of_value.

  Lemma of_value_with_Fatal
    (γ0 : string.String.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_precompile::interface::PrecompileError::Fatal" [
      γ0
    ] =
    φ (Fatal γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Fatal : of_value.

  Lemma of_value_with_Other
    (γ0 : borrow.Cow.t str.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_precompile::interface::PrecompileError::Other" [
      γ0
    ] =
    φ (Other γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Other : of_value.

  Definition of_value_OutOfGas :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::OutOfGas" []
    ).
  Proof. econstructor; apply of_value_with_OutOfGas; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfGas : of_value.

  Definition of_value_Blake2WrongLength :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Blake2WrongLength" []
    ).
  Proof. econstructor; apply of_value_with_Blake2WrongLength; eassumption. Defined.
  Smpl Add simple apply of_value_Blake2WrongLength : of_value.

  Definition of_value_Blake2WrongFinalIndicatorFlag :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Blake2WrongFinalIndicatorFlag" []
    ).
  Proof. econstructor; apply of_value_with_Blake2WrongFinalIndicatorFlag; eassumption. Defined.
  Smpl Add simple apply of_value_Blake2WrongFinalIndicatorFlag : of_value.

  Definition of_value_ModexpExpOverflow :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpExpOverflow" []
    ).
  Proof. econstructor; apply of_value_with_ModexpExpOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_ModexpExpOverflow : of_value.

  Definition of_value_ModexpBaseOverflow :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpBaseOverflow" []
    ).
  Proof. econstructor; apply of_value_with_ModexpBaseOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_ModexpBaseOverflow : of_value.

  Definition of_value_ModexpModOverflow :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpModOverflow" []
    ).
  Proof. econstructor; apply of_value_with_ModexpModOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_ModexpModOverflow : of_value.

  Definition of_value_ModexpEip7823LimitSize :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpEip7823LimitSize" []
    ).
  Proof. econstructor; apply of_value_with_ModexpEip7823LimitSize; eassumption. Defined.
  Smpl Add simple apply of_value_ModexpEip7823LimitSize : of_value.

  Definition of_value_Bn254FieldPointNotAMember :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bn254FieldPointNotAMember" []
    ).
  Proof. econstructor; apply of_value_with_Bn254FieldPointNotAMember; eassumption. Defined.
  Smpl Add simple apply of_value_Bn254FieldPointNotAMember : of_value.

  Definition of_value_Bn254AffineGFailedToCreate :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bn254AffineGFailedToCreate" []
    ).
  Proof. econstructor; apply of_value_with_Bn254AffineGFailedToCreate; eassumption. Defined.
  Smpl Add simple apply of_value_Bn254AffineGFailedToCreate : of_value.

  Definition of_value_Bn254PairLength :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bn254PairLength" []
    ).
  Proof. econstructor; apply of_value_with_Bn254PairLength; eassumption. Defined.
  Smpl Add simple apply of_value_Bn254PairLength : of_value.

  Definition of_value_BlobInvalidInputLength :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::BlobInvalidInputLength" []
    ).
  Proof. econstructor; apply of_value_with_BlobInvalidInputLength; eassumption. Defined.
  Smpl Add simple apply of_value_BlobInvalidInputLength : of_value.

  Definition of_value_BlobMismatchedVersion :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::BlobMismatchedVersion" []
    ).
  Proof. econstructor; apply of_value_with_BlobMismatchedVersion; eassumption. Defined.
  Smpl Add simple apply of_value_BlobMismatchedVersion : of_value.

  Definition of_value_BlobVerifyKzgProofFailed :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::BlobVerifyKzgProofFailed" []
    ).
  Proof. econstructor; apply of_value_with_BlobVerifyKzgProofFailed; eassumption. Defined.
  Smpl Add simple apply of_value_BlobVerifyKzgProofFailed : of_value.

  Definition of_value_NonCanonicalFp :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::NonCanonicalFp" []
    ).
  Proof. econstructor; apply of_value_with_NonCanonicalFp; eassumption. Defined.
  Smpl Add simple apply of_value_NonCanonicalFp : of_value.

  Definition of_value_Bls12381G1NotOnCurve :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G1NotOnCurve" []
    ).
  Proof. econstructor; apply of_value_with_Bls12381G1NotOnCurve; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12381G1NotOnCurve : of_value.

  Definition of_value_Bls12381G1NotInSubgroup :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G1NotInSubgroup" []
    ).
  Proof. econstructor; apply of_value_with_Bls12381G1NotInSubgroup; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12381G1NotInSubgroup : of_value.

  Definition of_value_Bls12381G2NotOnCurve :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G2NotOnCurve" []
    ).
  Proof. econstructor; apply of_value_with_Bls12381G2NotOnCurve; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12381G2NotOnCurve : of_value.

  Definition of_value_Bls12381G2NotInSubgroup :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G2NotInSubgroup" []
    ).
  Proof. econstructor; apply of_value_with_Bls12381G2NotInSubgroup; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12381G2NotInSubgroup : of_value.

  Definition of_value_Bls12381ScalarInputLength :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381ScalarInputLength" []
    ).
  Proof. econstructor; apply of_value_with_Bls12381ScalarInputLength; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12381ScalarInputLength : of_value.

  Definition of_value_Bls12381G1AddInputLength :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G1AddInputLength" []
    ).
  Proof. econstructor; apply of_value_with_Bls12381G1AddInputLength; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12381G1AddInputLength : of_value.

  Definition of_value_Bls12381G1MsmInputLength :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G1MsmInputLength" []
    ).
  Proof. econstructor; apply of_value_with_Bls12381G1MsmInputLength; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12381G1MsmInputLength : of_value.

  Definition of_value_Bls12381G2AddInputLength :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G2AddInputLength" []
    ).
  Proof. econstructor; apply of_value_with_Bls12381G2AddInputLength; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12381G2AddInputLength : of_value.

  Definition of_value_Bls12381G2MsmInputLength :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G2MsmInputLength" []
    ).
  Proof. econstructor; apply of_value_with_Bls12381G2MsmInputLength; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12381G2MsmInputLength : of_value.

  Definition of_value_Bls12381PairingInputLength :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381PairingInputLength" []
    ).
  Proof. econstructor; apply of_value_with_Bls12381PairingInputLength; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12381PairingInputLength : of_value.

  Definition of_value_Bls12381MapFpToG1InputLength :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381MapFpToG1InputLength" []
    ).
  Proof. econstructor; apply of_value_with_Bls12381MapFpToG1InputLength; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12381MapFpToG1InputLength : of_value.

  Definition of_value_Bls12381MapFp2ToG2InputLength :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381MapFp2ToG2InputLength" []
    ).
  Proof. econstructor; apply of_value_with_Bls12381MapFp2ToG2InputLength; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12381MapFp2ToG2InputLength : of_value.

  Definition of_value_Bls12381FpPaddingInvalid :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381FpPaddingInvalid" []
    ).
  Proof. econstructor; apply of_value_with_Bls12381FpPaddingInvalid; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12381FpPaddingInvalid : of_value.

  Definition of_value_Bls12381FpPaddingLength :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381FpPaddingLength" []
    ).
  Proof. econstructor; apply of_value_with_Bls12381FpPaddingLength; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12381FpPaddingLength : of_value.

  Definition of_value_Bls12381G1PaddingLength :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G1PaddingLength" []
    ).
  Proof. econstructor; apply of_value_with_Bls12381G1PaddingLength; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12381G1PaddingLength : of_value.

  Definition of_value_Bls12381G2PaddingLength :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bls12381G2PaddingLength" []
    ).
  Proof. econstructor; apply of_value_with_Bls12381G2PaddingLength; eassumption. Defined.
  Smpl Add simple apply of_value_Bls12381G2PaddingLength : of_value.

  Definition of_value_KzgInvalidG1Point :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::KzgInvalidG1Point" []
    ).
  Proof. econstructor; apply of_value_with_KzgInvalidG1Point; eassumption. Defined.
  Smpl Add simple apply of_value_KzgInvalidG1Point : of_value.

  Definition of_value_KzgG1PointNotOnCurve :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::KzgG1PointNotOnCurve" []
    ).
  Proof. econstructor; apply of_value_with_KzgG1PointNotOnCurve; eassumption. Defined.
  Smpl Add simple apply of_value_KzgG1PointNotOnCurve : of_value.

  Definition of_value_KzgG1PointNotInSubgroup :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::KzgG1PointNotInSubgroup" []
    ).
  Proof. econstructor; apply of_value_with_KzgG1PointNotInSubgroup; eassumption. Defined.
  Smpl Add simple apply of_value_KzgG1PointNotInSubgroup : of_value.

  Definition of_value_KzgInvalidInputLength :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::KzgInvalidInputLength" []
    ).
  Proof. econstructor; apply of_value_with_KzgInvalidInputLength; eassumption. Defined.
  Smpl Add simple apply of_value_KzgInvalidInputLength : of_value.

  Definition of_value_Secp256k1RecoverFailed :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Secp256k1RecoverFailed" []
    ).
  Proof. econstructor; apply of_value_with_Secp256k1RecoverFailed; eassumption. Defined.
  Smpl Add simple apply of_value_Secp256k1RecoverFailed : of_value.

  Definition of_value_Fatal
    (γ0 : string.String.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Fatal" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Fatal; eassumption. Defined.
  Smpl Add simple apply of_value_Fatal : of_value.

  Definition of_value_Other
    (γ0 : borrow.Cow.t str.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Other" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Other; eassumption. Defined.
  Smpl Add simple apply of_value_Other : of_value.

  Module SubPointer.
    Definition get_Fatal_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_precompile::interface::PrecompileError::Fatal" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Fatal γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : string.String.t) :=
        match γ with
        | Fatal _ => Some (Fatal γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Fatal_0_is_valid : SubPointer.Runner.Valid.t get_Fatal_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Fatal_0_is_valid : run_sub_pointer.

    Definition get_Other_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_precompile::interface::PrecompileError::Other" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Other γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : borrow.Cow.t str.t) :=
        match γ with
        | Other _ => Some (Other γ_0)
        | _ => None
        end;
    |}.

    Lemma get_Other_0_is_valid : SubPointer.Runner.Valid.t get_Other_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Other_0_is_valid : run_sub_pointer.
  End SubPointer.
End PrecompileError.

Module Precompiles.
  Record t : Set := {
    inner: map.HashMap.t address.Address.t revm_precompile.Precompile.t random.RandomState.t;
    addresses: set.HashSet.t address.Address.t random.RandomState.t;
    optimized_access: vec.Vec.t (option.Option.t revm_precompile.Precompile.t) alloc.Global.t;
    all_short_addresses: bool;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_precompile::Precompiles";
    φ '(Build_t inner addresses optimized_access all_short_addresses) :=
      Value.StructRecord "revm_precompile::Precompiles" [
        ("inner", φ inner);
        ("addresses", φ addresses);
        ("optimized_access", φ optimized_access);
        ("all_short_addresses", φ all_short_addresses)
      ]
  }.
End Precompiles.

Module Precompile.
  Record t : Set := {
    id: id.PrecompileId.t;
    address: address.Address.t;
    fn_: Function2.t ('& (slice.t U8.t)) U64.t (result.Result.t interface.PrecompileOutput.t interface.PrecompileError.t);
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_precompile::Precompile";
    φ '(Build_t id address fn_) :=
      Value.StructRecord "revm_precompile::Precompile" [
        ("id", φ id);
        ("address", φ address);
        ("fn_", φ fn_)
      ]
  }.
End Precompile.

Module PrecompileSpecId.
  Inductive t : Set :=
  | HOMESTEAD
  | BYZANTIUM
  | ISTANBUL
  | BERLIN
  | CANCUN
  | PRAGUE
  | OSAKA
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_precompile::PrecompileSpecId";
    φ x :=
      match x with
      | HOMESTEAD =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::HOMESTEAD" []
      | BYZANTIUM =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::BYZANTIUM" []
      | ISTANBUL =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::ISTANBUL" []
      | BERLIN =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::BERLIN" []
      | CANCUN =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::CANCUN" []
      | PRAGUE =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::PRAGUE" []
      | OSAKA =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::OSAKA" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_precompile::PrecompileSpecId").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_HOMESTEAD :
    Value.StructTuple "revm_precompile::PrecompileSpecId::HOMESTEAD" [] =
    φ HOMESTEAD.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_HOMESTEAD : of_value.

  Lemma of_value_with_BYZANTIUM :
    Value.StructTuple "revm_precompile::PrecompileSpecId::BYZANTIUM" [] =
    φ BYZANTIUM.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BYZANTIUM : of_value.

  Lemma of_value_with_ISTANBUL :
    Value.StructTuple "revm_precompile::PrecompileSpecId::ISTANBUL" [] =
    φ ISTANBUL.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ISTANBUL : of_value.

  Lemma of_value_with_BERLIN :
    Value.StructTuple "revm_precompile::PrecompileSpecId::BERLIN" [] =
    φ BERLIN.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BERLIN : of_value.

  Lemma of_value_with_CANCUN :
    Value.StructTuple "revm_precompile::PrecompileSpecId::CANCUN" [] =
    φ CANCUN.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CANCUN : of_value.

  Lemma of_value_with_PRAGUE :
    Value.StructTuple "revm_precompile::PrecompileSpecId::PRAGUE" [] =
    φ PRAGUE.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PRAGUE : of_value.

  Lemma of_value_with_OSAKA :
    Value.StructTuple "revm_precompile::PrecompileSpecId::OSAKA" [] =
    φ OSAKA.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OSAKA : of_value.

  Definition of_value_HOMESTEAD :
    OfValue.t (
      Value.StructTuple "revm_precompile::PrecompileSpecId::HOMESTEAD" []
    ).
  Proof. econstructor; apply of_value_with_HOMESTEAD; eassumption. Defined.
  Smpl Add simple apply of_value_HOMESTEAD : of_value.

  Definition of_value_BYZANTIUM :
    OfValue.t (
      Value.StructTuple "revm_precompile::PrecompileSpecId::BYZANTIUM" []
    ).
  Proof. econstructor; apply of_value_with_BYZANTIUM; eassumption. Defined.
  Smpl Add simple apply of_value_BYZANTIUM : of_value.

  Definition of_value_ISTANBUL :
    OfValue.t (
      Value.StructTuple "revm_precompile::PrecompileSpecId::ISTANBUL" []
    ).
  Proof. econstructor; apply of_value_with_ISTANBUL; eassumption. Defined.
  Smpl Add simple apply of_value_ISTANBUL : of_value.

  Definition of_value_BERLIN :
    OfValue.t (
      Value.StructTuple "revm_precompile::PrecompileSpecId::BERLIN" []
    ).
  Proof. econstructor; apply of_value_with_BERLIN; eassumption. Defined.
  Smpl Add simple apply of_value_BERLIN : of_value.

  Definition of_value_CANCUN :
    OfValue.t (
      Value.StructTuple "revm_precompile::PrecompileSpecId::CANCUN" []
    ).
  Proof. econstructor; apply of_value_with_CANCUN; eassumption. Defined.
  Smpl Add simple apply of_value_CANCUN : of_value.

  Definition of_value_PRAGUE :
    OfValue.t (
      Value.StructTuple "revm_precompile::PrecompileSpecId::PRAGUE" []
    ).
  Proof. econstructor; apply of_value_with_PRAGUE; eassumption. Defined.
  Smpl Add simple apply of_value_PRAGUE : of_value.

  Definition of_value_OSAKA :
    OfValue.t (
      Value.StructTuple "revm_precompile::PrecompileSpecId::OSAKA" []
    ).
  Proof. econstructor; apply of_value_with_OSAKA; eassumption. Defined.
  Smpl Add simple apply of_value_OSAKA : of_value.

  Module SubPointer.

  End SubPointer.
End PrecompileSpecId.

Module SpecId.
  Inductive t : Set :=
  | FRONTIER
  | FRONTIER_THAWING
  | HOMESTEAD
  | DAO_FORK
  | TANGERINE
  | SPURIOUS_DRAGON
  | BYZANTIUM
  | CONSTANTINOPLE
  | PETERSBURG
  | ISTANBUL
  | MUIR_GLACIER
  | BERLIN
  | LONDON
  | ARROW_GLACIER
  | GRAY_GLACIER
  | MERGE
  | SHANGHAI
  | CANCUN
  | PRAGUE
  | OSAKA
  | AMSTERDAM
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_primitives::hardfork::SpecId";
    φ x :=
      match x with
      | FRONTIER =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::FRONTIER" []
      | FRONTIER_THAWING =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::FRONTIER_THAWING" []
      | HOMESTEAD =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::HOMESTEAD" []
      | DAO_FORK =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::DAO_FORK" []
      | TANGERINE =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::TANGERINE" []
      | SPURIOUS_DRAGON =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::SPURIOUS_DRAGON" []
      | BYZANTIUM =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::BYZANTIUM" []
      | CONSTANTINOPLE =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::CONSTANTINOPLE" []
      | PETERSBURG =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::PETERSBURG" []
      | ISTANBUL =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::ISTANBUL" []
      | MUIR_GLACIER =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::MUIR_GLACIER" []
      | BERLIN =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::BERLIN" []
      | LONDON =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::LONDON" []
      | ARROW_GLACIER =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::ARROW_GLACIER" []
      | GRAY_GLACIER =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::GRAY_GLACIER" []
      | MERGE =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::MERGE" []
      | SHANGHAI =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::SHANGHAI" []
      | CANCUN =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::CANCUN" []
      | PRAGUE =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::PRAGUE" []
      | OSAKA =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::OSAKA" []
      | AMSTERDAM =>
        Value.StructTuple "revm_primitives::hardfork::SpecId::AMSTERDAM" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_primitives::hardfork::SpecId").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_FRONTIER :
    Value.StructTuple "revm_primitives::hardfork::SpecId::FRONTIER" [] =
    φ FRONTIER.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_FRONTIER : of_value.

  Lemma of_value_with_FRONTIER_THAWING :
    Value.StructTuple "revm_primitives::hardfork::SpecId::FRONTIER_THAWING" [] =
    φ FRONTIER_THAWING.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_FRONTIER_THAWING : of_value.

  Lemma of_value_with_HOMESTEAD :
    Value.StructTuple "revm_primitives::hardfork::SpecId::HOMESTEAD" [] =
    φ HOMESTEAD.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_HOMESTEAD : of_value.

  Lemma of_value_with_DAO_FORK :
    Value.StructTuple "revm_primitives::hardfork::SpecId::DAO_FORK" [] =
    φ DAO_FORK.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_DAO_FORK : of_value.

  Lemma of_value_with_TANGERINE :
    Value.StructTuple "revm_primitives::hardfork::SpecId::TANGERINE" [] =
    φ TANGERINE.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_TANGERINE : of_value.

  Lemma of_value_with_SPURIOUS_DRAGON :
    Value.StructTuple "revm_primitives::hardfork::SpecId::SPURIOUS_DRAGON" [] =
    φ SPURIOUS_DRAGON.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_SPURIOUS_DRAGON : of_value.

  Lemma of_value_with_BYZANTIUM :
    Value.StructTuple "revm_primitives::hardfork::SpecId::BYZANTIUM" [] =
    φ BYZANTIUM.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BYZANTIUM : of_value.

  Lemma of_value_with_CONSTANTINOPLE :
    Value.StructTuple "revm_primitives::hardfork::SpecId::CONSTANTINOPLE" [] =
    φ CONSTANTINOPLE.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CONSTANTINOPLE : of_value.

  Lemma of_value_with_PETERSBURG :
    Value.StructTuple "revm_primitives::hardfork::SpecId::PETERSBURG" [] =
    φ PETERSBURG.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PETERSBURG : of_value.

  Lemma of_value_with_ISTANBUL :
    Value.StructTuple "revm_primitives::hardfork::SpecId::ISTANBUL" [] =
    φ ISTANBUL.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ISTANBUL : of_value.

  Lemma of_value_with_MUIR_GLACIER :
    Value.StructTuple "revm_primitives::hardfork::SpecId::MUIR_GLACIER" [] =
    φ MUIR_GLACIER.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MUIR_GLACIER : of_value.

  Lemma of_value_with_BERLIN :
    Value.StructTuple "revm_primitives::hardfork::SpecId::BERLIN" [] =
    φ BERLIN.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BERLIN : of_value.

  Lemma of_value_with_LONDON :
    Value.StructTuple "revm_primitives::hardfork::SpecId::LONDON" [] =
    φ LONDON.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_LONDON : of_value.

  Lemma of_value_with_ARROW_GLACIER :
    Value.StructTuple "revm_primitives::hardfork::SpecId::ARROW_GLACIER" [] =
    φ ARROW_GLACIER.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ARROW_GLACIER : of_value.

  Lemma of_value_with_GRAY_GLACIER :
    Value.StructTuple "revm_primitives::hardfork::SpecId::GRAY_GLACIER" [] =
    φ GRAY_GLACIER.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_GRAY_GLACIER : of_value.

  Lemma of_value_with_MERGE :
    Value.StructTuple "revm_primitives::hardfork::SpecId::MERGE" [] =
    φ MERGE.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MERGE : of_value.

  Lemma of_value_with_SHANGHAI :
    Value.StructTuple "revm_primitives::hardfork::SpecId::SHANGHAI" [] =
    φ SHANGHAI.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_SHANGHAI : of_value.

  Lemma of_value_with_CANCUN :
    Value.StructTuple "revm_primitives::hardfork::SpecId::CANCUN" [] =
    φ CANCUN.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CANCUN : of_value.

  Lemma of_value_with_PRAGUE :
    Value.StructTuple "revm_primitives::hardfork::SpecId::PRAGUE" [] =
    φ PRAGUE.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PRAGUE : of_value.

  Lemma of_value_with_OSAKA :
    Value.StructTuple "revm_primitives::hardfork::SpecId::OSAKA" [] =
    φ OSAKA.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OSAKA : of_value.

  Lemma of_value_with_AMSTERDAM :
    Value.StructTuple "revm_primitives::hardfork::SpecId::AMSTERDAM" [] =
    φ AMSTERDAM.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_AMSTERDAM : of_value.

  Definition of_value_FRONTIER :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::FRONTIER" []
    ).
  Proof. econstructor; apply of_value_with_FRONTIER; eassumption. Defined.
  Smpl Add simple apply of_value_FRONTIER : of_value.

  Definition of_value_FRONTIER_THAWING :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::FRONTIER_THAWING" []
    ).
  Proof. econstructor; apply of_value_with_FRONTIER_THAWING; eassumption. Defined.
  Smpl Add simple apply of_value_FRONTIER_THAWING : of_value.

  Definition of_value_HOMESTEAD :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::HOMESTEAD" []
    ).
  Proof. econstructor; apply of_value_with_HOMESTEAD; eassumption. Defined.
  Smpl Add simple apply of_value_HOMESTEAD : of_value.

  Definition of_value_DAO_FORK :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::DAO_FORK" []
    ).
  Proof. econstructor; apply of_value_with_DAO_FORK; eassumption. Defined.
  Smpl Add simple apply of_value_DAO_FORK : of_value.

  Definition of_value_TANGERINE :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::TANGERINE" []
    ).
  Proof. econstructor; apply of_value_with_TANGERINE; eassumption. Defined.
  Smpl Add simple apply of_value_TANGERINE : of_value.

  Definition of_value_SPURIOUS_DRAGON :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::SPURIOUS_DRAGON" []
    ).
  Proof. econstructor; apply of_value_with_SPURIOUS_DRAGON; eassumption. Defined.
  Smpl Add simple apply of_value_SPURIOUS_DRAGON : of_value.

  Definition of_value_BYZANTIUM :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::BYZANTIUM" []
    ).
  Proof. econstructor; apply of_value_with_BYZANTIUM; eassumption. Defined.
  Smpl Add simple apply of_value_BYZANTIUM : of_value.

  Definition of_value_CONSTANTINOPLE :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::CONSTANTINOPLE" []
    ).
  Proof. econstructor; apply of_value_with_CONSTANTINOPLE; eassumption. Defined.
  Smpl Add simple apply of_value_CONSTANTINOPLE : of_value.

  Definition of_value_PETERSBURG :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::PETERSBURG" []
    ).
  Proof. econstructor; apply of_value_with_PETERSBURG; eassumption. Defined.
  Smpl Add simple apply of_value_PETERSBURG : of_value.

  Definition of_value_ISTANBUL :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::ISTANBUL" []
    ).
  Proof. econstructor; apply of_value_with_ISTANBUL; eassumption. Defined.
  Smpl Add simple apply of_value_ISTANBUL : of_value.

  Definition of_value_MUIR_GLACIER :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::MUIR_GLACIER" []
    ).
  Proof. econstructor; apply of_value_with_MUIR_GLACIER; eassumption. Defined.
  Smpl Add simple apply of_value_MUIR_GLACIER : of_value.

  Definition of_value_BERLIN :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::BERLIN" []
    ).
  Proof. econstructor; apply of_value_with_BERLIN; eassumption. Defined.
  Smpl Add simple apply of_value_BERLIN : of_value.

  Definition of_value_LONDON :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::LONDON" []
    ).
  Proof. econstructor; apply of_value_with_LONDON; eassumption. Defined.
  Smpl Add simple apply of_value_LONDON : of_value.

  Definition of_value_ARROW_GLACIER :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::ARROW_GLACIER" []
    ).
  Proof. econstructor; apply of_value_with_ARROW_GLACIER; eassumption. Defined.
  Smpl Add simple apply of_value_ARROW_GLACIER : of_value.

  Definition of_value_GRAY_GLACIER :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::GRAY_GLACIER" []
    ).
  Proof. econstructor; apply of_value_with_GRAY_GLACIER; eassumption. Defined.
  Smpl Add simple apply of_value_GRAY_GLACIER : of_value.

  Definition of_value_MERGE :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::MERGE" []
    ).
  Proof. econstructor; apply of_value_with_MERGE; eassumption. Defined.
  Smpl Add simple apply of_value_MERGE : of_value.

  Definition of_value_SHANGHAI :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::SHANGHAI" []
    ).
  Proof. econstructor; apply of_value_with_SHANGHAI; eassumption. Defined.
  Smpl Add simple apply of_value_SHANGHAI : of_value.

  Definition of_value_CANCUN :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::CANCUN" []
    ).
  Proof. econstructor; apply of_value_with_CANCUN; eassumption. Defined.
  Smpl Add simple apply of_value_CANCUN : of_value.

  Definition of_value_PRAGUE :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::PRAGUE" []
    ).
  Proof. econstructor; apply of_value_with_PRAGUE; eassumption. Defined.
  Smpl Add simple apply of_value_PRAGUE : of_value.

  Definition of_value_OSAKA :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::OSAKA" []
    ).
  Proof. econstructor; apply of_value_with_OSAKA; eassumption. Defined.
  Smpl Add simple apply of_value_OSAKA : of_value.

  Definition of_value_AMSTERDAM :
    OfValue.t (
      Value.StructTuple "revm_primitives::hardfork::SpecId::AMSTERDAM" []
    ).
  Proof. econstructor; apply of_value_with_AMSTERDAM; eassumption. Defined.
  Smpl Add simple apply of_value_AMSTERDAM : of_value.

  Module SubPointer.

  End SubPointer.
End SpecId.

Module AccountInfo.
  Record t : Set := {
    balance: ruint.Uint.t 256 4;
    nonce: U64.t;
    code_hash: fixed.FixedBytes.t 32;
    code: option.Option.t bytecode.Bytecode.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_state::account_info::AccountInfo";
    φ '(Build_t balance nonce code_hash code) :=
      Value.StructRecord "revm_state::account_info::AccountInfo" [
        ("balance", φ balance);
        ("nonce", φ nonce);
        ("code_hash", φ code_hash);
        ("code", φ code)
      ]
  }.
End AccountInfo.

Module Account.
  Record t : Set := {
    info: account_info.AccountInfo.t;
    transaction_id: Usize.t;
    storage: map.HashMap.t (ruint.Uint.t 256 4) revm_state.EvmStorageSlot.t random.RandomState.t;
    status: revm_state.AccountStatus.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_state::Account";
    φ '(Build_t info transaction_id storage status) :=
      Value.StructRecord "revm_state::Account" [
        ("info", φ info);
        ("transaction_id", φ transaction_id);
        ("storage", φ storage);
        ("status", φ status)
      ]
  }.
End Account.

Module EvmStorageSlot.
  Record t : Set := {
    original_value: ruint.Uint.t 256 4;
    present_value: ruint.Uint.t 256 4;
    transaction_id: Usize.t;
    is_cold: bool;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_state::EvmStorageSlot";
    φ '(Build_t original_value present_value transaction_id is_cold) :=
      Value.StructRecord "revm_state::EvmStorageSlot" [
        ("original_value", φ original_value);
        ("present_value", φ present_value);
        ("transaction_id", φ transaction_id);
        ("is_cold", φ is_cold)
      ]
  }.
End EvmStorageSlot.
