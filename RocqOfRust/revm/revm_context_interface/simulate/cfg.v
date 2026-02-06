Require Import simulate.RocqOfRust.
Require Import revm.revm_context_interface.links.cfg.

Module Cfg.
  Class C
      (Self : Set) `{Link Self}
      (types : Cfg.Types.t) `{Cfg.Types.AreLinks types} :
      Type := {
    chain_id : Self -> u64;
    spec : Self -> types.(Cfg.Types.Spec);
    max_code_size : Self -> usize;
    is_eip3607_disabled : Self -> bool;
    is_balance_check_disabled : Self -> bool;
    is_gas_refund_disabled : Self -> bool;
    is_block_gas_limit_disabled : Self -> bool;
    is_nonce_check_disabled : Self -> bool;
    is_base_fee_check_disabled : Self -> bool;
  }.

  Module Eq.
    Class t
        {Self : Set} `{Link Self}
        {types : Cfg.Types.t} `{Cfg.Types.AreLinks types}
        (I : C Self types) :
        Prop := {
      chain_id
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!Cfg.Method_chain_id Self} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (Cfg.run_chain_id ref_self)
            stack 🌲
          (
            Output.Success (I.(chain_id) self),
            stack
          )
        }};
      spec
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!Cfg.Method_spec Self types} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (Cfg.run_spec ref_self)
            stack 🌲
          (
            Output.Success (I.(spec) self),
            stack
          )
        }};
      max_code_size
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!Cfg.Method_max_code_size Self} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (Cfg.run_max_code_size ref_self)
            stack 🌲
          (
            Output.Success (I.(max_code_size) self),
            stack
          )
        }};
      is_eip3607_disabled
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!Cfg.Method_is_eip3607_disabled Self} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (Cfg.run_is_eip3607_disabled ref_self)
            stack 🌲
          (
            Output.Success (I.(is_eip3607_disabled) self),
            stack
          )
        }};
      is_balance_check_disabled
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!Cfg.Method_is_balance_check_disabled Self} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (Cfg.run_is_balance_check_disabled ref_self)
            stack 🌲
          (
            Output.Success (I.(is_balance_check_disabled) self),
            stack
          )
        }};
      is_block_gas_limit_disabled
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!Cfg.Method_is_block_gas_limit_disabled Self} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (Cfg.run_is_block_gas_limit_disabled ref_self)
            stack 🌲
          (
            Output.Success (I.(is_block_gas_limit_disabled) self),
            stack
          )
        }};
      is_nonce_check_disabled
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!Cfg.Method_is_nonce_check_disabled Self} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (Cfg.run_is_nonce_check_disabled ref_self)
            stack 🌲
          (
            Output.Success (I.(is_nonce_check_disabled) self),
            stack
          )
        }};
      is_base_fee_check_disabled
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!Cfg.Method_is_base_fee_check_disabled Self} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (Cfg.run_is_base_fee_check_disabled ref_self)
            stack 🌲
          (
            Output.Success (I.(is_base_fee_check_disabled) self),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End Cfg.
Export (hints) Cfg.

Module CfgGetter.
  Class C
      (Self : Set) `{Link Self}
      (types : CfgGetter.Types.t)
      `{CfgGetter.Types.AreLinks types} :
      Type := {
    Cfg_for_Cfg :: Cfg.C types.(CfgGetter.Types.Cfg) (CfgGetter.Types.to_Cfg_types types);
    cfg : RefStub.t Self types.(CfgGetter.Types.Cfg);
  }.

  Module Eq.
    Class t
        {Self : Set} `{Link Self}
        {types : CfgGetter.Types.t}
        `{CfgGetter.Types.AreLinks types}
        (I : C Self types) :
        Prop := {
      Cfg_for_Cfg :: Cfg.Eq.t I.(Cfg_for_Cfg);
      cfg
          (stack : Stack.t)
          (ref_self : '& Self)
          `{!CfgGetter.Method_cfg Self types} :
        {{
          SimulateM.eval_f
            (CfgGetter.run_cfg ref_self)
            stack 🌲
          (
            Output.Success (RefStub.apply ref_self I.(cfg)),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End CfgGetter.
Export (hints) CfgGetter.
