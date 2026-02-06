Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.common.
Require Import core.links.error.
Require Import revm.revm_context_interface.links.transaction.

Module TransactionError.
  Class C (Self : Set) `{Link Self} : Set := {
    Error_for_Self :: Error.Run Self;
  }.

  Module Eq.
    Class t
        {Self : Set} `{Link Self}
        `{!Error.Run Self}
        (I : C Self) :
        Prop := {
      Error_for_Self : True;
    }.
  End Eq.
  Export (hints) Eq.
End TransactionError.
Export (hints) TransactionError.

Module Transaction.
  Class C
      (Self : Set) `{Link Self}
      (types : Transaction.Types.t)
      `{Transaction.Types.AreLinks types} :
      Set := {
    tx_type : Self -> types.(Transaction.Types.TransactionType);
    legacy : RefStub.t Self types.(Transaction.Types.Legacy);
    eip2930 : RefStub.t Self types.(Transaction.Types.Eip2930);
    eip1559 : RefStub.t Self types.(Transaction.Types.Eip1559);
    eip4844 : RefStub.t Self types.(Transaction.Types.Eip4844);
    eip7702 : RefStub.t Self types.(Transaction.Types.Eip7702);
    max_fee : Self -> u128;
    effective_gas_price : Self -> u128 -> u128;
    kind : Self -> TxKind.t;
    access_list : Self -> option (RefStub.t Self types.(Transaction.Types.AccessList));
  }.

  Module Eq.
    Class t
        {Self : Set} `{Link Self}
        {types : Transaction.Types.t}
        `{Transaction.Types.AreLinks types}
        (I : C Self types) :
        Prop := {
      tx_type
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!Transaction.Method_tx_type Self types} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (Transaction.run_tx_type ref_self)
            stack 🌲
          (
            Output.Success (I.(tx_type) self),
            stack
          )
        }};
      legacy
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!Transaction.Method_legacy Self types} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (Transaction.run_legacy ref_self)
            stack 🌲
          (
            Output.Success (RefStub.apply ref_self I.(legacy)),
            stack
          )
        }};
      eip2930
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!Transaction.Method_eip2930 Self types} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (Transaction.run_eip2930 ref_self)
            stack 🌲
          (
            Output.Success (RefStub.apply ref_self I.(eip2930)),
            stack
          )
        }};
      eip1559
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!Transaction.Method_eip1559 Self types} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (Transaction.run_eip1559 ref_self)
            stack 🌲
          (
            Output.Success (RefStub.apply ref_self I.(eip1559)),
            stack
          )
        }};
      eip4844
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!Transaction.Method_eip4844 Self types} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (Transaction.run_eip4844 ref_self)
            stack 🌲
          (
            Output.Success (RefStub.apply ref_self I.(eip4844)),
            stack
          )
        }};
      eip7702
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!Transaction.Method_eip7702 Self types} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (Transaction.run_eip7702 ref_self)
            stack 🌲
          (
            Output.Success (RefStub.apply ref_self I.(eip7702)),
            stack
          )
        }};
      max_fee
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!Transaction.Method_max_fee Self types} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (Transaction.run_max_fee ref_self)
            stack 🌲
          (
            Output.Success (I.(max_fee) self),
            stack
          )
        }};
      effective_gas_price
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          (base_fee : u128)
          `{!Transaction.Method_effective_gas_price Self types} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (Transaction.run_effective_gas_price ref_self base_fee)
            stack 🌲
          (
            Output.Success (I.(effective_gas_price) self base_fee),
            stack
          )
        }};
      kind
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!Transaction.Method_kind Self types} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (Transaction.run_kind ref_self)
            stack 🌲
          (
            Output.Success (I.(kind) self),
            stack
          )
        }};
      access_list
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!Transaction.Method_access_list Self types} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (Transaction.run_access_list ref_self)
            stack 🌲
          (
            Output.Success (
              option_map (RefStub.apply ref_self) (I.(access_list) self)
            ),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End Transaction.
Export (hints) Transaction.

Module TransactionGetter.
  Class C
      (Self : Set) `{Link Self}
      (Transaction : Set) `{Link Transaction}
      (types : Transaction.Types.t)
      `{Transaction.Types.AreLinks types} :
      Set := {
    Transaction_for_Transaction :: Transaction.C Transaction types;
    tx : RefStub.t Self Transaction;
  }.

  Module Eq.
    Class t
        {Self : Set} `{Link Self}
        {Transaction : Set} `{Link Transaction}
        {types : Transaction.Types.t}
        `{Transaction.Types.AreLinks types}
        (I : C Self Transaction types) :
        Prop := {
      Transaction_for_Transaction :: Transaction.Eq.t I.(Transaction_for_Transaction);
      tx
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!transaction.TransactionGetter.Method_tx Self Transaction} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (transaction.TransactionGetter.run_tx ref_self)
            stack 🌲
          (
            Output.Success (RefStub.apply ref_self I.(tx)),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End TransactionGetter.
Export (hints) TransactionGetter.

Module TransactionSetter.
  Class C
      (Self : Set) `{Link Self}
      (Transaction : Set) `{Link Transaction}
      (types : Transaction.Types.t)
      `{Transaction.Types.AreLinks types} :
      Set := {
    TransactionGetter_for_Self :: TransactionGetter.C Self Transaction types;
    set_tx : Self -> Transaction -> Self;
  }.

  Module Eq.
    Class t
        {Self : Set} `{Link Self}
        {Transaction : Set} `{Link Transaction}
        {types : Transaction.Types.t}
        `{Transaction.Types.AreLinks types}
        `{!transaction.TransactionSetter.Run Self Transaction types}
        (I : C Self Transaction types) :
        Prop := {
      TransactionGetter_for_Self ::
        TransactionGetter.Eq.t I.(TransactionGetter_for_Self);
      set_tx
          (self : Self)
          (tx : Transaction)
          (stack : Stack.t)
          `{!transaction.TransactionSetter.Method_set_tx Self Transaction} :
        let ref_self : '&mut Self := make_ref 0 in
        {{
          SimulateM.eval_f
            (transaction.TransactionSetter.run_set_tx ref_self tx)
            (self :: stack)%stack 🌲
          (
            Output.Success tt,
            (I.(set_tx) self tx :: stack)%stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End TransactionSetter.
Export (hints) TransactionSetter.
