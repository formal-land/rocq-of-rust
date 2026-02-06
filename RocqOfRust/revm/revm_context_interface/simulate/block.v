Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_context_interface.block.links.blob.
Require Import revm.revm_context_interface.links.block.

Module Block.
  Class C (Self : Set) `{Link Self} : Type := {
    number : Self -> u64;
    beneficiary : Self -> Address.t;
    timestamp : Self -> u64;
    gas_limit : Self -> u64;
    basefee : Self -> u64;
    difficulty : Self -> aliases.U256.t;
    prevrandao : Self -> option aliases.B256.t;
    blob_excess_gas_and_price : Self -> option BlobExcessGasAndPrice.t;
    blob_gasprice : Self -> option u128;
    blob_excess_gas : Self -> option u64;
  }.

  Module Eq.
    Class t
        {Self : Set} `{Link Self}
        (I : C Self) :
        Prop := {
      number
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!block.Block.Method_number Self} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (block.Block.run_number ref_self)
            stack 🌲
          (
            Output.Success (I.(number) self),
            stack
          )
        }};
      beneficiary
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!block.Block.Method_beneficiary Self} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (block.Block.run_beneficiary ref_self)
            stack 🌲
          (
            Output.Success (I.(beneficiary) self),
            stack
          )
        }};
      timestamp
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!block.Block.Method_timestamp Self} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (block.Block.run_timestamp ref_self)
            stack 🌲
          (
            Output.Success (I.(timestamp) self),
            stack
          )
        }};
      gas_limit
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!block.Block.Method_gas_limit Self} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (block.Block.run_gas_limit ref_self)
            stack 🌲
          (
            Output.Success (I.(gas_limit) self),
            stack
          )
        }};
      basefee
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!block.Block.Method_basefee Self} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (block.Block.run_basefee ref_self)
            stack 🌲
          (
            Output.Success (I.(basefee) self),
            stack
          )
        }};
      difficulty
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!block.Block.Method_difficulty Self} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (block.Block.run_difficulty ref_self)
            stack 🌲
          (
            Output.Success (I.(difficulty) self),
            stack
          )
        }};
      prevrandao
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!block.Block.Method_prevrandao Self} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (block.Block.run_prevrandao ref_self)
            stack 🌲
          (
            Output.Success (I.(prevrandao) self),
            stack
          )
        }};
      blob_excess_gas_and_price
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!block.Block.Method_blob_excess_gas_and_price Self} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (block.Block.run_blob_excess_gas_and_price ref_self)
            stack 🌲
          (
            Output.Success (I.(blob_excess_gas_and_price) self),
            stack
          )
        }};
      blob_gasprice
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!block.Block.Method_blob_gasprice Self} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (block.Block.run_blob_gasprice ref_self)
            stack 🌲
          (
            Output.Success (I.(blob_gasprice) self),
            stack
          )
        }};
      blob_excess_gas
          (stack : Stack.t)
          (ref_self : '& Self)
          (self : Self)
          `{!block.Block.Method_blob_excess_gas Self} :
        CanRead.t stack self ref_self ->
        {{
          SimulateM.eval_f
            (block.Block.run_blob_excess_gas ref_self)
            stack 🌲
          (
            Output.Success (I.(blob_excess_gas) self),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End Block.
Export (hints) Block.

Module BlockGetter.
  Class C
      (Self : Set) `{Link Self}
      (types : block.BlockGetter.Types.t)
      `{block.BlockGetter.Types.AreLinks types} :
      Type := {
    Block_for_Block :: Block.C types.(block.BlockGetter.Types.Block);
    block : RefStub.t Self types.(block.BlockGetter.Types.Block);
  }.

  Module Eq.
    Class t
        {Self : Set} `{Link Self}
        {types : block.BlockGetter.Types.t}
        `{block.BlockGetter.Types.AreLinks types}
        (I : C Self types) :
        Prop := {
      Block_for_Block :: Block.Eq.t I.(Block_for_Block);
      block
          (stack : Stack.t)
          (ref_self : '& Self)
          `{!block.BlockGetter.Method_block Self types} :
        {{
          SimulateM.eval_f
            (block.BlockGetter.run_block ref_self)
            stack 🌲
          (
            Output.Success (RefStub.apply ref_self I.(block)),
            stack
          )
        }};
    }.
  End Eq.
  Export (hints) Eq.
End BlockGetter.
Export (hints) BlockGetter.
