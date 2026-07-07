Require Import simulate.RocqOfRust.
Require Import alloc.simulate.boxed.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.ops.simulate.deref.
Require Import revm.revm_context_interface.links.cfg.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.contract.create.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.interpreter_action.links.create_inputs.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.

Definition finish_create
    (IS_CREATE2 : bool)
    (value : aliases.U256.t)
    (len : usize)
    (init_code : alloy_primitives.bytes.links.mod.Bytes.t)
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  if IS_CREATE2 then
    popn_macro interpreter 1
      (fun interpreter => (interpreter, host)) (fun arr interpreter =>
    let '⟬ salt ⟭ := arr.(array.value) in
    gas_or_fail_macro interpreter (calc.create2_cost len)
      (fun interpreter => (interpreter, host)) (fun interpreter =>
    let gas_limit :=
      if
        Impl_SpecId.is_enabled_in
          (IInterpreterTypes
              .(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
              .(RuntimeFlag.spec_id)
            interpreter.(Interpreter.runtime_flag))
          SpecId.TANGERINE
      then
        interpreter.(Interpreter.gas).(Gas.remaining) -i
          interpreter.(Interpreter.gas).(Gas.remaining) /i 64
      else
        interpreter.(Interpreter.gas).(Gas.remaining) in
    gas_macro interpreter gas_limit
      (fun interpreter => (interpreter, host)) (fun interpreter =>
    let caller :=
      IInterpreterTypes
        .(InterpreterTypes.InputsTrait_for_Input)
        .(InputTraits.target_address)
        interpreter.(Interpreter.input) in
    let bytecode :=
      IInterpreterTypes
        .(InterpreterTypes.LoopControl_for_Bytecode)
        .(LoopControl.set_action)
        interpreter.(Interpreter.bytecode)
        (interpreter_action.InterpreterAction.NewFrame
          (interpreter_action.FrameInput.Create
            (Impl_Box.new {|
              create_inputs.CreateInputs.caller := caller;
              create_inputs.CreateInputs.scheme := CreateScheme.Create2 salt;
              create_inputs.CreateInputs.value := value;
              create_inputs.CreateInputs.init_code := init_code;
              create_inputs.CreateInputs.gas_limit := gas_limit;
            |}))) in
    (interpreter <| Interpreter.bytecode := bytecode |>, host)
    )))
  else
    gas_macro interpreter constants.CREATE
      (fun interpreter => (interpreter, host)) (fun interpreter =>
    let gas_limit :=
      if
        Impl_SpecId.is_enabled_in
          (IInterpreterTypes
              .(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
              .(RuntimeFlag.spec_id)
            interpreter.(Interpreter.runtime_flag))
          SpecId.TANGERINE
      then
        interpreter.(Interpreter.gas).(Gas.remaining) -i
          interpreter.(Interpreter.gas).(Gas.remaining) /i 64
      else
        interpreter.(Interpreter.gas).(Gas.remaining) in
    gas_macro interpreter gas_limit
      (fun interpreter => (interpreter, host)) (fun interpreter =>
    let caller :=
      IInterpreterTypes
        .(InterpreterTypes.InputsTrait_for_Input)
        .(InputTraits.target_address)
        interpreter.(Interpreter.input) in
    let bytecode :=
      IInterpreterTypes
        .(InterpreterTypes.LoopControl_for_Bytecode)
        .(LoopControl.set_action)
        interpreter.(Interpreter.bytecode)
        (interpreter_action.InterpreterAction.NewFrame
          (interpreter_action.FrameInput.Create
            (Impl_Box.new {|
              create_inputs.CreateInputs.caller := caller;
              create_inputs.CreateInputs.scheme := CreateScheme.Create;
              create_inputs.CreateInputs.value := value;
              create_inputs.CreateInputs.init_code := init_code;
              create_inputs.CreateInputs.gas_limit := gas_limit;
            |}))) in
    (interpreter <| Interpreter.bytecode := bytecode |>, host)
    )).

Definition create
    (IS_CREATE2 : bool)
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  require_non_staticcall_macro interpreter
    (fun interpreter => (interpreter, host)) (fun interpreter =>
  if IS_CREATE2 then
    check_macro interpreter SpecId.PETERSBURG
      (fun interpreter => (interpreter, host)) (fun interpreter =>
    popn_macro interpreter 3
      (fun interpreter => (interpreter, host)) (fun arr interpreter =>
    let '⟬ value; code_offset; len ⟭ := arr.(array.value) in
    as_usize_or_fail_macro interpreter len None
      (fun interpreter => (interpreter, host)) (fun len interpreter =>
    if i[len] =? 0 then
      finish_create IS_CREATE2 value len Impl_Bytes.new interpreter host
    else
      if
        Impl_SpecId.is_enabled_in
          (IInterpreterTypes
              .(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
              .(RuntimeFlag.spec_id)
            interpreter.(Interpreter.runtime_flag))
          SpecId.SHANGHAI
      then
        let '(max_initcode_size, host) := IHost.(Host.max_initcode_size) host in
        if i[len] >? i[max_initcode_size] then
          (halt interpreter instruction_result.InstructionResult.CreateInitCodeSizeLimit, host)
        else
          gas_macro interpreter (calc.initcode_cost len)
            (fun interpreter => (interpreter, host)) (fun interpreter =>
          as_usize_or_fail_macro interpreter code_offset None
            (fun interpreter => (interpreter, host)) (fun code_offset interpreter =>
          resize_memory_macro interpreter code_offset len
            (fun interpreter => (interpreter, host)) (fun interpreter =>
          let slice :=
            IInterpreterTypes
              .(InterpreterTypes.MemoryTrait_for_Memory)
              .(MemoryTrait.slice_len)
              interpreter.(Interpreter.memory)
              code_offset
              len in
          let data :=
            IInterpreterTypes
              .(InterpreterTypes.MemoryTrait_for_Memory)
              .(MemoryTrait.Deref_for_Synthetic)
              .(Deref.deref)
              .(RefStub.projection)
              slice in
          finish_create IS_CREATE2 value len (Impl_Bytes.copy_from_slice data) interpreter host
          )))
      else
        as_usize_or_fail_macro interpreter code_offset None
          (fun interpreter => (interpreter, host)) (fun code_offset interpreter =>
        resize_memory_macro interpreter code_offset len
          (fun interpreter => (interpreter, host)) (fun interpreter =>
        let slice :=
          IInterpreterTypes
            .(InterpreterTypes.MemoryTrait_for_Memory)
            .(MemoryTrait.slice_len)
            interpreter.(Interpreter.memory)
            code_offset
            len in
        let data :=
          IInterpreterTypes
            .(InterpreterTypes.MemoryTrait_for_Memory)
            .(MemoryTrait.Deref_for_Synthetic)
            .(Deref.deref)
            .(RefStub.projection)
            slice in
        finish_create IS_CREATE2 value len (Impl_Bytes.copy_from_slice data) interpreter host
        ))
    )))
  else
    popn_macro interpreter 3
      (fun interpreter => (interpreter, host)) (fun arr interpreter =>
    let '⟬ value; code_offset; len ⟭ := arr.(array.value) in
    as_usize_or_fail_macro interpreter len None
      (fun interpreter => (interpreter, host)) (fun len interpreter =>
    if i[len] =? 0 then
      finish_create IS_CREATE2 value len Impl_Bytes.new interpreter host
    else
      if
        Impl_SpecId.is_enabled_in
          (IInterpreterTypes
              .(InterpreterTypes.RuntimeFlag_for_RuntimeFlag)
              .(RuntimeFlag.spec_id)
            interpreter.(Interpreter.runtime_flag))
          SpecId.SHANGHAI
      then
        let '(max_initcode_size, host) := IHost.(Host.max_initcode_size) host in
        if i[len] >? i[max_initcode_size] then
          (halt interpreter instruction_result.InstructionResult.CreateInitCodeSizeLimit, host)
        else
          gas_macro interpreter (calc.initcode_cost len)
            (fun interpreter => (interpreter, host)) (fun interpreter =>
          as_usize_or_fail_macro interpreter code_offset None
            (fun interpreter => (interpreter, host)) (fun code_offset interpreter =>
          resize_memory_macro interpreter code_offset len
            (fun interpreter => (interpreter, host)) (fun interpreter =>
          let slice :=
            IInterpreterTypes
              .(InterpreterTypes.MemoryTrait_for_Memory)
              .(MemoryTrait.slice_len)
              interpreter.(Interpreter.memory)
              code_offset
              len in
          let data :=
            IInterpreterTypes
              .(InterpreterTypes.MemoryTrait_for_Memory)
              .(MemoryTrait.Deref_for_Synthetic)
              .(Deref.deref)
              .(RefStub.projection)
              slice in
          finish_create IS_CREATE2 value len (Impl_Bytes.copy_from_slice data) interpreter host
          )))
      else
        as_usize_or_fail_macro interpreter code_offset None
          (fun interpreter => (interpreter, host)) (fun code_offset interpreter =>
        resize_memory_macro interpreter code_offset len
          (fun interpreter => (interpreter, host)) (fun interpreter =>
        let slice :=
          IInterpreterTypes
            .(InterpreterTypes.MemoryTrait_for_Memory)
            .(MemoryTrait.slice_len)
            interpreter.(Interpreter.memory)
            code_offset
            len in
        let data :=
          IInterpreterTypes
            .(InterpreterTypes.MemoryTrait_for_Memory)
            .(MemoryTrait.Deref_for_Synthetic)
            .(Deref.deref)
            .(RefStub.projection)
            slice in
        finish_create IS_CREATE2 value len (Impl_Bytes.copy_from_slice data) interpreter host
        ))
    ))).

Lemma create_eq
    (IS_CREATE2 : bool)
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (run_Host_for_H : Host.Run H H_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (IHost : Host.C H H_types)
    (HostEq : Host.Eq.t IHost)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  let context := {|
    instruction_context.InstructionContext.interpreter := ref_interpreter;
    instruction_context.InstructionContext.host := ref_host;
  |} in
  {{
    SimulateM.eval_f (
      run_create
        IS_CREATE2 run_InterpreterTypes_for_WIRE run_Host_for_H context
      )
      [interpreter; host]%stack 🌲
    (
      Output.Success tt,
      let (interpreter, host) := create IS_CREATE2 interpreter host in
      [interpreter; host]%stack
    )
  }}.
Proof.
Admitted.
