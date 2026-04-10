Require Import links.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.links.common.
Require Import core.convert.links.mod.
Require Import core.links.error.
Require Import core.links.option.
Require Import revm.revm_context_interface.transaction.links.common.
Require Import revm.revm_context_interface.transaction.links.eip4844.
Require Import revm.revm_context_interface.transaction.links.transaction_type.

(* pub trait TransactionError: Debug + core::error::Error {} *)
Module TransactionError.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_context_interface::transaction::TransactionError";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Run (Self : Set) `{Link Self} : Set := {
    run_Error_for_Self : Error.Run Self;
  }.
End TransactionError.

(*
pub trait Transaction {
    type TransactionError: TransactionError;
    type TransactionType: Into<TransactionType>;
    type AccessList: AccessListTrait;
    type Legacy: LegacyTx;
    type Eip2930: Eip2930Tx<AccessList = Self::AccessList>;
    type Eip1559: Eip1559Tx<AccessList = Self::AccessList>;
    type Eip4844: Eip4844Tx<AccessList = Self::AccessList>;
    type Eip7702: Eip7702Tx<AccessList = Self::AccessList>;

    fn tx_type(&self) -> Self::TransactionType;
    fn legacy(&self) -> &Self::Legacy;
    fn eip2930(&self) -> &Self::Eip2930;
    fn eip1559(&self) -> &Self::Eip1559;
    fn eip4844(&self) -> &Self::Eip4844;
    fn eip7702(&self) -> &Self::Eip7702;
    fn common_fields(&self) -> &dyn CommonTxFields
    fn max_fee(&self) -> u128
    fn effective_gas_price(&self, base_fee: u128) -> u128
    fn kind(&self) -> TxKind
    fn access_list(&self) -> Option<&Self::AccessList>
}
*)
Module Transaction.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_context_interface::transaction::Transaction";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Module Types.
    Record t : Type := {
      TransactionError : Set;
      TransactionType : Set;
      AccessList : Set;
      Legacy : Set;
      Eip2930 : Set;
      Eip1559 : Set;
      Eip4844 : Set;
      Eip7702 : Set;
    }.

    Class AreLinks (types : t) : Set := {
      H_TransactionError :: Link types.(TransactionError);
      H_TransactionType :: Link types.(TransactionType);
      H_AccessList :: Link types.(AccessList);
      H_Legacy :: Link types.(Legacy);
      H_Eip2930 :: Link types.(Eip2930);
      H_Eip1559 :: Link types.(Eip1559);
      H_Eip4844 :: Link types.(Eip4844);
      H_Eip7702 :: Link types.(Eip7702);
    }.
  End Types.
  Export (hints) Types.

  Class Method_tx_type (Self : Set) `{Link Self} (types : Types.t) `{Types.AreLinks types} : Set := {
    tx_type : PolymorphicFunction.t;
    tx_type_is_method :: IsTraitMethod.C (trait Self) "tx_type" tx_type;
    run_tx_type (self : '& Self) :: Run.Trait tx_type [] [] [ φ self ] types.(Types.TransactionType);
  }.

  Class Method_legacy (Self : Set) `{Link Self} (types : Types.t) `{Types.AreLinks types} : Set := {
    legacy : PolymorphicFunction.t;
    legacy_is_method :: IsTraitMethod.C (trait Self) "legacy" legacy;
    run_legacy (self : '& Self) :: Run.Trait legacy [] [] [ φ self ] ('& types.(Types.Legacy));
  }.

  Class Method_eip2930 (Self : Set) `{Link Self} (types : Types.t) `{Types.AreLinks types} : Set := {
    eip2930 : PolymorphicFunction.t;
    eip2930_is_method :: IsTraitMethod.C (trait Self) "eip2930" eip2930;
    run_eip2930 (self : '& Self) :: Run.Trait eip2930 [] [] [ φ self ] ('& types.(Types.Eip2930));
  }.

  Class Method_eip1559 (Self : Set) `{Link Self} (types : Types.t) `{Types.AreLinks types} : Set := {
    eip1559 : PolymorphicFunction.t;
    eip1559_is_method :: IsTraitMethod.C (trait Self) "eip1559" eip1559;
    run_eip1559 (self : '& Self) :: Run.Trait eip1559 [] [] [ φ self ] ('& types.(Types.Eip1559));
  }.

  Class Method_eip4844 (Self : Set) `{Link Self} (types : Types.t) `{Types.AreLinks types} : Set := {
    eip4844 : PolymorphicFunction.t;
    eip4844_is_method :: IsTraitMethod.C (trait Self) "eip4844" eip4844;
    run_eip4844 (self : '& Self) :: Run.Trait eip4844 [] [] [ φ self ] ('& types.(Types.Eip4844));
  }.

  Class Method_eip7702 (Self : Set) `{Link Self} (types : Types.t) `{Types.AreLinks types} : Set := {
    eip7702 : PolymorphicFunction.t;
    eip7702_is_method :: IsTraitMethod.C (trait Self) "eip7702" eip7702;
    run_eip7702 (self : '& Self) :: Run.Trait eip7702 [] [] [ φ self ] ('& types.(Types.Eip7702));
  }.

  Module dyn_CommonTxFields.
    Record t {Self : Set} : Set := {
      H : Link Self;
      run : CommonTxFields.Run Self;
    }.
    Arguments t : clear implicits.

    Instance IsLink : Link {Self: Set @ t Self} := {
      Φ := Ty.dyn [("revm_context_interface::transaction::common::CommonTxFields", [], [])];
      φ x := Value.StructTuple "revm_context_interface::transaction::common::CommonTxFields" [] [] [];
    }.
  End dyn_CommonTxFields.
  Export (hints) dyn_CommonTxFields.

  Class Method_common_fields (Self : Set) `{Link Self} (types : Types.t) `{Types.AreLinks types} : Set := {
    common_fields : PolymorphicFunction.t;
    common_fields_is_method :: IsTraitMethod.C (trait Self) "common_fields" common_fields;
    run_common_fields (self : '& Self) ::
      Run.Trait common_fields [] [] [ φ self ] ('& {Self : Set @ dyn_CommonTxFields.t Self});
  }.

  Class Method_max_fee (Self : Set) `{Link Self} (types : Types.t) `{Types.AreLinks types} : Set := {
    max_fee : PolymorphicFunction.t;
    max_fee_is_method :: IsTraitMethod.C (trait Self) "max_fee" max_fee;
    run_max_fee (self : '& Self) :: Run.Trait max_fee [] [] [ φ self ] u128;
  }.

  Class Method_effective_gas_price (Self : Set) `{Link Self} (types : Types.t) `{Types.AreLinks types} : Set := {
    effective_gas_price : PolymorphicFunction.t;
    effective_gas_price_is_method :: IsTraitMethod.C (trait Self) "effective_gas_price" effective_gas_price;
    run_effective_gas_price (self : '& Self) (base_fee : u128) :: Run.Trait effective_gas_price [] [] [ φ self; φ base_fee ] u128;
  }.

  Class Method_kind (Self : Set) `{Link Self} (types : Types.t) `{Types.AreLinks types} : Set := {
    kind : PolymorphicFunction.t;
    kind_is_method :: IsTraitMethod.C (trait Self) "kind" kind;
    run_kind (self : '& Self) :: Run.Trait kind [] [] [ φ self ] TxKind.t;
  }.

  Class Method_access_list (Self : Set) `{Link Self} (types : Types.t) `{Types.AreLinks types} : Set := {
    access_list : PolymorphicFunction.t;
    access_list_is_method :: IsTraitMethod.C (trait Self) "access_list" access_list;
    run_access_list (self : '& Self) :: Run.Trait access_list [] [] [ φ self ] (option ('& types.(Types.AccessList)));
  }.

  Class Run
      (Self : Set) `{Link Self}
      (types : Types.t) `{Types.AreLinks types} :
      Set := {
    TransactionError_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::transaction::Transaction" [] [] (Φ Self)
        "TransactionError" (Φ types.(Types.TransactionError));
    TransactionType_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::transaction::Transaction" [] [] (Φ Self)
        "TransactionType" (Φ types.(Types.TransactionType));
    run_Into_for_TransactionType :
      Into.Run types.(Types.TransactionType) TransactionType.t;
    AccessList_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::transaction::Transaction" [] [] (Φ Self)
        "AccessList" (Φ types.(Types.AccessList));
    Legacy_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::transaction::Transaction" [] [] (Φ Self)
        "Legacy" (Φ types.(Types.Legacy));
    Eip2930_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::transaction::Transaction" [] [] (Φ Self)
        "Eip2930" (Φ types.(Types.Eip2930));
    Eip1559_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::transaction::Transaction" [] [] (Φ Self)
        "Eip1559" (Φ types.(Types.Eip1559));
    Eip4844_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::transaction::Transaction" [] [] (Φ Self)
        "Eip4844" (Φ types.(Types.Eip4844));
    run_Eip4844Tx_for_Eip4844 :: Eip4844Tx.Run types.(Types.Eip4844);
    Eip7702_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::transaction::Transaction" [] [] (Φ Self)
        "Eip7702" (Φ types.(Types.Eip7702));
    method_tx_type :: Method_tx_type Self types;
    method_legacy :: Method_legacy Self types;
    method_eip2930 :: Method_eip2930 Self types;
    method_eip1559 :: Method_eip1559 Self types;
    method_eip4844 :: Method_eip4844 Self types;
    method_eip7702 :: Method_eip7702 Self types;
    method_common_fields :: Method_common_fields Self types;
    method_max_fee :: Method_max_fee Self types;
    method_effective_gas_price :: Method_effective_gas_price Self types;
    method_kind :: Method_kind Self types;
    method_access_list :: Method_access_list Self types;
  }.
End Transaction.
Export (hints) Transaction.

Module Impl_Transaction_for_Ref_Transaction.
  Instance run
    (Self : Set) `{Link Self}
    (types : Transaction.Types.t) `{Transaction.Types.AreLinks types}
    (run_Transaction_for_Self : Transaction.Run Self types) :
    Transaction.Run ('& Self) types.
  Admitted.
End Impl_Transaction_for_Ref_Transaction.

(*
pub trait TransactionGetter {
    type Transaction: Transaction;

    fn tx(&self) -> &Self::Transaction;
}
*)
Module TransactionGetter.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_context_interface::transaction::TransactionGetter";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_tx (Self : Set) `{Link Self} (Transaction : Set) `{Link Transaction} : Set := {
    tx : PolymorphicFunction.t;
    tx_is_method :: IsTraitMethod.C (trait Self) "tx" tx;
    run_tx (self : '& Self) :: Run.Trait tx [] [] [ φ self ] ('& Transaction);
  }.

  Class Run
      (Self : Set) `{Link Self}
      (Transaction : Set) `{Link Transaction}
      (types : Transaction.Types.t) `{Transaction.Types.AreLinks types} :
      Set := {
    Transaction_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::transaction::TransactionGetter" [] [] (Φ Self)
        "Transaction" (Φ Transaction);
    run_Transaction_for_Transaction ::
      Transaction.Run Transaction types;
    method_tx :: Method_tx Self Transaction;
  }.
End TransactionGetter.
Export (hints) TransactionGetter.

(*
pub trait TransactionSetter: TransactionGetter {
    fn set_tx(&mut self, tx: <Self as TransactionGetter>::Transaction);
}
*)
Module TransactionSetter.
  Definition trait (Self : Set) `{Link Self} : TraitHeader.t :=
    {|
      TraitHeader.trait_name := "revm_context_interface::transaction::TransactionSetter";
      TraitHeader.trait_consts := [];
      TraitHeader.trait_tys := [];
      TraitHeader.self_ty := Φ Self;
    |}.

  Class Method_set_tx (Self : Set) `{Link Self} (Transaction : Set) `{Link Transaction} : Set := {
    set_tx : PolymorphicFunction.t;
    set_tx_is_method :: IsTraitMethod.C (trait Self) "set_tx" set_tx;
    run_set_tx (self : '&mut Self) (tx : Transaction) :: Run.Trait set_tx [] [] [ φ self; φ tx ] unit;
  }.

  Class Run
      (Self : Set) `{Link Self}
      (Transaction : Set) `{Link Transaction}
      (types : Transaction.Types.t) `{Transaction.Types.AreLinks types} :
      Set := {
    run_TransactionGetter_for_Self ::
      TransactionGetter.Run Self Transaction types;
    method_set_tx :: Method_set_tx Self Transaction;
  }.
End TransactionSetter.
Export (hints) TransactionSetter.
