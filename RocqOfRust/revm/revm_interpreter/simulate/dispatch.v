Require Import Stdlib.Lists.List.

Require Import RocqOfRust.revm.revm_interpreter.interpreter.
Require Import simulate.RocqOfRust.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.add.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.div.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.mul.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.sub.
Require Import revm.revm_interpreter.instructions.simulate.control.stop.
Require Import revm.revm_interpreter.instructions.simulate.control.unknown.
Require Import revm.revm_interpreter.instructions.simulate.table.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.links.table.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.simulate.interpreter.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_interpreter.simulate.step.

Module InterpreterDispatch.
  Definition OpcodeInSimple (opcode : u8) : Prop :=
    opcode.(Integer.value) = 0 \/
    opcode.(Integer.value) = 1 \/
    opcode.(Integer.value) = 2 \/
    opcode.(Integer.value) = 3 \/
    opcode.(Integer.value) = 4.

  Definition BytecodeInSimple (code : list u8) : Prop :=
    List.Forall OpcodeInSimple code.

  Record TableValid
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (table :
        array.t
          (Instruction.t WIRE H WIRE_types)
          {| Integer.value := 256 |}) : Prop := {
    table_stop :
      exists instruction,
        InterpreterStep.instruction_at
          table
          {| Integer.value := 0 |} =
          Some instruction /\
        InterpreterStep.instruction_static_gas instruction =
          {| Integer.value := 0 |};
    table_add :
      exists instruction,
        InterpreterStep.instruction_at
          table
          {| Integer.value := 1 |} =
          Some instruction /\
        InterpreterStep.instruction_static_gas instruction =
          {| Integer.value := 3 |};
    table_mul :
      exists instruction,
        InterpreterStep.instruction_at
          table
          {| Integer.value := 2 |} =
          Some instruction /\
        InterpreterStep.instruction_static_gas instruction =
          {| Integer.value := 5 |};
    table_sub :
      exists instruction,
        InterpreterStep.instruction_at
          table
          {| Integer.value := 3 |} =
          Some instruction /\
        InterpreterStep.instruction_static_gas instruction =
          {| Integer.value := 3 |};
    table_div :
      exists instruction,
        InterpreterStep.instruction_at
          table
          {| Integer.value := 4 |} =
          Some instruction /\
        InterpreterStep.instruction_static_gas instruction =
          {| Integer.value := 5 |};
  }.

  Definition simple
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      `{IInterpreterTypes : InterpreterTypes.C WIRE_types}
      (opcode : u8)
      (state : InstructionContext.State.t H WIRE WIRE_types) :
      InstructionContext.State.t H WIRE WIRE_types :=
    InstructionContext.map_interpreter
      (if Z.eqb opcode.(Integer.value) 0 then
        stop
      else if Z.eqb opcode.(Integer.value) 1 then
        add
      else if Z.eqb opcode.(Integer.value) 2 then
        mul
      else if Z.eqb opcode.(Integer.value) 3 then
        sub
      else if Z.eqb opcode.(Integer.value) 4 then
        div
      else
        unknown)
      state.

  Lemma simple_stop
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      `{IInterpreterTypes : InterpreterTypes.C WIRE_types}
      (state : InstructionContext.State.t H WIRE WIRE_types) :
    simple {| Integer.value := 0 |} state =
    InstructionContext.map_interpreter stop state.
  Proof.
    reflexivity.
  Qed.

  Lemma simple_add
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      `{IInterpreterTypes : InterpreterTypes.C WIRE_types}
      (state : InstructionContext.State.t H WIRE WIRE_types) :
    simple {| Integer.value := 1 |} state =
    InstructionContext.map_interpreter add state.
  Proof.
    reflexivity.
  Qed.

  Lemma simple_sub
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      `{IInterpreterTypes : InterpreterTypes.C WIRE_types}
      (state : InstructionContext.State.t H WIRE WIRE_types) :
    simple {| Integer.value := 3 |} state =
    InstructionContext.map_interpreter sub state.
  Proof.
    reflexivity.
  Qed.

  Lemma simple_mul
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      `{IInterpreterTypes : InterpreterTypes.C WIRE_types}
      (state : InstructionContext.State.t H WIRE WIRE_types) :
    simple {| Integer.value := 2 |} state =
    InstructionContext.map_interpreter mul state.
  Proof.
    reflexivity.
  Qed.

  Lemma simple_div
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      `{IInterpreterTypes : InterpreterTypes.C WIRE_types}
      (state : InstructionContext.State.t H WIRE WIRE_types) :
    simple {| Integer.value := 4 |} state =
    InstructionContext.map_interpreter div state.
  Proof.
    reflexivity.
  Qed.

  Definition step_result_simple
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (IInterpreterTypes : InterpreterTypes.C WIRE_types)
      (table :
        array.t
          (Instruction.t WIRE H WIRE_types)
          {| Integer.value := 256 |})
      (state : InstructionContext.State.t H WIRE WIRE_types) :
      InterpreterStep.Result.t H WIRE WIRE_types :=
    InterpreterStep.step_result
      IInterpreterTypes
      (fun opcode state =>
        simple
          (IInterpreterTypes := IInterpreterTypes)
          opcode
          state)
      table
      state.

  Definition result_state
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (initial_state : InstructionContext.State.t H WIRE WIRE_types)
      (result : InterpreterStep.Result.t H WIRE WIRE_types) :
      InstructionContext.State.t H WIRE WIRE_types :=
    match result with
    | InterpreterStep.Result.MissingInstruction => initial_state
    | InterpreterStep.Result.OutOfGas state => state
    | InterpreterStep.Result.Success state => state
    end.

  Definition stack_with_table
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (table :
        array.t
          (Instruction.t WIRE H WIRE_types)
          {| Integer.value := 256 |})
      (state : InstructionContext.State.t H WIRE WIRE_types) :
      Stack.t :=
    match state with
    | {|
        InstructionContext.State.interpreter := interpreter;
        InstructionContext.State.host := host
      |} =>
        [interpreter; table; host]%stack
    end.

  Lemma step_simple_eq
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types)
      (IInterpreterTypes : InterpreterTypes.C WIRE_types)
      (InterpreterTypesEq :
        InterpreterTypes.Eq.t
          WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
      (state : InstructionContext.State.t H WIRE WIRE_types) :
    let table :=
      FragmentInstructionTable.table
        (H := H)
        run_InterpreterTypes_for_WIRE in
    let final_state :=
      result_state state
        (step_result_simple IInterpreterTypes table state) in
    let ref_interpreter :
      '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
    let ref_table :
      '& (array.t
        (Instruction.t WIRE H WIRE_types)
        {| Integer.value := 256 |}) := make_ref 1 in
    let ref_host : '&mut H := make_ref 2 in
    {{
      SimulateM.eval_f
        (Impl_Interpreter.run_step
          WIRE H
          ref_interpreter
          ref_table
          ref_host)
        (stack_with_table table state) 🌲
      (
        Output.Success tt,
        stack_with_table table final_state
      )
    }}.
  Proof.
    (* Admitted boundary: translated Interpreter::step to the semantic step. *)
  Admitted.

  Definition take_next_action
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (IInterpreterTypes : InterpreterTypes.C WIRE_types)
      (state : InstructionContext.State.t H WIRE WIRE_types) :
      InterpreterAction.t *
        InstructionContext.State.t H WIRE WIRE_types :=
    match state with
    | {|
        InstructionContext.State.interpreter := interpreter;
        InstructionContext.State.host := host
      |} =>
        let '(action, bytecode) :=
          IInterpreterTypes
            .(InterpreterTypes.LoopControl_for_Bytecode)
            .(LoopControl.take_next_action)
            interpreter.(Interpreter.bytecode) in
        (action, {|
          InstructionContext.State.interpreter :=
            interpreter <| Interpreter.bytecode := bytecode |>;
          InstructionContext.State.host := host;
        |})
    end.

  Definition finish_if_halted
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (IInterpreterTypes : InterpreterTypes.C WIRE_types)
      (is_not_end :
        WIRE_types.(InterpreterTypes.Types.Bytecode) -> bool)
      (state : InstructionContext.State.t H WIRE WIRE_types) :
      option
        (InterpreterAction.t *
          InstructionContext.State.t H WIRE WIRE_types) :=
    match state with
    | {|
        InstructionContext.State.interpreter := interpreter;
        InstructionContext.State.host := _
      |} =>
        if is_not_end interpreter.(Interpreter.bytecode)
        then None
        else Some (take_next_action IInterpreterTypes state)
    end.

  Fixpoint run_plain_fuel
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (fuel : nat)
      (IInterpreterTypes : InterpreterTypes.C WIRE_types)
      (is_not_end :
        WIRE_types.(InterpreterTypes.Types.Bytecode) -> bool)
      (table :
        array.t
          (Instruction.t WIRE H WIRE_types)
          {| Integer.value := 256 |})
      (state : InstructionContext.State.t H WIRE WIRE_types) :
      option
        (InterpreterAction.t *
          InstructionContext.State.t H WIRE WIRE_types) :=
    match finish_if_halted IInterpreterTypes is_not_end state with
    | Some result => Some result
    | None =>
        match fuel with
        | O => None
        | S fuel =>
            match step_result_simple IInterpreterTypes table state with
            | InterpreterStep.Result.MissingInstruction => None
            | InterpreterStep.Result.OutOfGas state
            | InterpreterStep.Result.Success state =>
                run_plain_fuel
                  fuel IInterpreterTypes is_not_end table state
            end
        end
    end.

  Instance run_run_plain
      (WIRE H : Set) `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types}
      (self : '&mut (Interpreter.t WIRE WIRE_types))
      (instruction_table :
        '& (array.t
          (Instruction.t WIRE H WIRE_types)
          {| Integer.value := 256 |}))
      (host : '&mut H) :
    Run.Trait
      (RocqOfRust.revm.revm_interpreter.interpreter.interpreter
        .Impl_revm_interpreter_interpreter_Interpreter_IW
        .run_plain (Φ WIRE))
      []
      [Φ H]
      [φ self; φ instruction_table; φ host]
      InterpreterAction.t.
  Proof.
    (* Admitted boundary: the translated unbounded run_plain loop. *)
  Admitted.
  Global Opaque run_run_plain.

  Definition RunPlainEvaluation
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types)
      (initial_state final_state :
        InstructionContext.State.t H WIRE WIRE_types)
      (action : InterpreterAction.t) : Prop :=
    let table :=
      FragmentInstructionTable.table
        (H := H)
        run_InterpreterTypes_for_WIRE in
    let ref_interpreter :
      '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
    let ref_table :
      '& (array.t
        (Instruction.t WIRE H WIRE_types)
        {| Integer.value := 256 |}) := make_ref 1 in
    let ref_host : '&mut H := make_ref 2 in
    {{
      SimulateM.eval_f
        (run_run_plain
          (run_InterpreterTypes_for_WIRE :=
            run_InterpreterTypes_for_WIRE)
          WIRE H
          ref_interpreter
          ref_table
          ref_host)
        (stack_with_table table initial_state) 🌲
      (
        Output.Success action,
        stack_with_table table final_state
      )
    }}.

  Lemma run_plain_eq
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types)
      (IInterpreterTypes : InterpreterTypes.C WIRE_types)
      (is_not_end :
        WIRE_types.(InterpreterTypes.Types.Bytecode) -> bool)
      (InterpreterTypesEq :
        InterpreterTypes.Eq.t
          WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
      (fuel : nat)
      (initial_state final_state :
        InstructionContext.State.t H WIRE WIRE_types)
      (action : InterpreterAction.t)
      (H_run :
        run_plain_fuel
          fuel
          IInterpreterTypes
          is_not_end
          (FragmentInstructionTable.table
            (H := H)
            run_InterpreterTypes_for_WIRE)
          initial_state =
        Some (action, final_state)) :
    RunPlainEvaluation
      run_InterpreterTypes_for_WIRE
      initial_state
      final_state
      action.
  Proof.
    (* Admitted boundary: iteration of step_simple_eq and take_next_action. *)
  Admitted.

  Lemma step_result_success
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (IInterpreterTypes : InterpreterTypes.C WIRE_types)
      (table :
        array.t
          (Instruction.t WIRE H WIRE_types)
          {| Integer.value := 256 |})
      (interpreter : Interpreter.t WIRE WIRE_types)
      (host : H)
      (opcode : u8)
      (instruction : Instruction.t WIRE H WIRE_types)
      (static_gas : u64)
      (gas : Gas.t)
      (operation :
        Interpreter.t WIRE WIRE_types ->
        Interpreter.t WIRE WIRE_types)
      (H_dispatch :
        forall state : InstructionContext.State.t H WIRE WIRE_types,
          simple
            (IInterpreterTypes := IInterpreterTypes)
            opcode state =
          InstructionContext.map_interpreter operation state)
      (H_opcode :
        IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode)
          .(Jumps.opcode) interpreter.(Interpreter.bytecode) =
        opcode)
      (H_instruction :
        InterpreterStep.instruction_at table opcode =
        Some instruction)
      (H_static_gas :
        InterpreterStep.instruction_static_gas instruction =
        static_gas)
      (H_charge :
        Impl_Gas.record_cost interpreter.(Interpreter.gas) static_gas =
        Some gas) :
    step_result_simple IInterpreterTypes table
      {|
        InstructionContext.State.interpreter := interpreter;
        InstructionContext.State.host := host;
      |} =
    InterpreterStep.Result.Success
      (InstructionContext.map_interpreter operation
        {|
          InstructionContext.State.interpreter :=
            (interpreter
                <| Interpreter.bytecode :=
                  IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode)
                    .(Jumps.relative_jump)
                    interpreter.(Interpreter.bytecode)
                    {| Integer.value := 1 |}
                |>)
              <| Interpreter.gas := gas |>;
          InstructionContext.State.host := host;
        |}).
  Proof.
    destruct interpreter.
    cbn in H_charge.
    unfold step_result_simple, InterpreterStep.step_result,
      InterpreterStep.prepare.
    rewrite H_opcode, H_instruction, H_static_gas.
    cbn in H_charge |- *.
    rewrite H_charge, H_dispatch.
    reflexivity.
  Qed.

  Lemma step_result_stop
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (IInterpreterTypes : InterpreterTypes.C WIRE_types)
      (table :
        array.t
          (Instruction.t WIRE H WIRE_types)
          {| Integer.value := 256 |})
      (interpreter : Interpreter.t WIRE WIRE_types)
      (host : H)
      (instruction : Instruction.t WIRE H WIRE_types)
      (gas : Gas.t)
      (H_opcode :
        IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode)
          .(Jumps.opcode) interpreter.(Interpreter.bytecode) =
        {| Integer.value := 0 |})
      (H_instruction :
        InterpreterStep.instruction_at table {| Integer.value := 0 |} =
        Some instruction)
      (H_gas :
        InterpreterStep.instruction_static_gas instruction =
        {| Integer.value := 0 |})
      (H_charge :
        Impl_Gas.record_cost
          interpreter.(Interpreter.gas)
          {| Integer.value := 0 |} =
        Some gas) :
    step_result_simple IInterpreterTypes table
      {|
        InstructionContext.State.interpreter := interpreter;
        InstructionContext.State.host := host;
      |} =
    InterpreterStep.Result.Success
      (InstructionContext.map_interpreter stop
        {|
          InstructionContext.State.interpreter :=
            (interpreter
                <| Interpreter.bytecode :=
                  IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode)
                    .(Jumps.relative_jump)
                    interpreter.(Interpreter.bytecode)
                    {| Integer.value := 1 |}
                |>)
              <| Interpreter.gas := gas |>;
          InstructionContext.State.host := host;
        |}).
  Proof.
    eapply step_result_success
      with
        (opcode := {| Integer.value := 0 |})
        (instruction := instruction)
        (static_gas := {| Integer.value := 0 |});
      try eassumption.
    intros state.
    apply simple_stop.
  Qed.

  Lemma step_result_add
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (IInterpreterTypes : InterpreterTypes.C WIRE_types)
      (table :
        array.t
          (Instruction.t WIRE H WIRE_types)
          {| Integer.value := 256 |})
      (interpreter : Interpreter.t WIRE WIRE_types)
      (host : H)
      (instruction : Instruction.t WIRE H WIRE_types)
      (gas : Gas.t)
      (H_opcode :
        IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode)
          .(Jumps.opcode) interpreter.(Interpreter.bytecode) =
        {| Integer.value := 1 |})
      (H_instruction :
        InterpreterStep.instruction_at table {| Integer.value := 1 |} =
        Some instruction)
      (H_gas :
        InterpreterStep.instruction_static_gas instruction =
        {| Integer.value := 3 |})
      (H_charge :
        Impl_Gas.record_cost
          interpreter.(Interpreter.gas)
          {| Integer.value := 3 |} =
        Some gas) :
    step_result_simple IInterpreterTypes table
      {|
        InstructionContext.State.interpreter := interpreter;
        InstructionContext.State.host := host;
      |} =
    InterpreterStep.Result.Success
      (InstructionContext.map_interpreter add
        {|
          InstructionContext.State.interpreter :=
            (interpreter
                <| Interpreter.bytecode :=
                  IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode)
                    .(Jumps.relative_jump)
                    interpreter.(Interpreter.bytecode)
                    {| Integer.value := 1 |}
                |>)
              <| Interpreter.gas := gas |>;
          InstructionContext.State.host := host;
        |}).
  Proof.
    eapply step_result_success
      with
        (opcode := {| Integer.value := 1 |})
        (instruction := instruction)
        (static_gas := {| Integer.value := 3 |});
      try eassumption.
    intros state.
    apply simple_add.
  Qed.

  Lemma step_result_sub
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (IInterpreterTypes : InterpreterTypes.C WIRE_types)
      (table :
        array.t
          (Instruction.t WIRE H WIRE_types)
          {| Integer.value := 256 |})
      (interpreter : Interpreter.t WIRE WIRE_types)
      (host : H)
      (instruction : Instruction.t WIRE H WIRE_types)
      (gas : Gas.t)
      (H_opcode :
        IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode)
          .(Jumps.opcode) interpreter.(Interpreter.bytecode) =
        {| Integer.value := 3 |})
      (H_instruction :
        InterpreterStep.instruction_at table {| Integer.value := 3 |} =
        Some instruction)
      (H_gas :
        InterpreterStep.instruction_static_gas instruction =
        {| Integer.value := 3 |})
      (H_charge :
        Impl_Gas.record_cost
          interpreter.(Interpreter.gas)
          {| Integer.value := 3 |} =
        Some gas) :
    step_result_simple IInterpreterTypes table
      {|
        InstructionContext.State.interpreter := interpreter;
        InstructionContext.State.host := host;
      |} =
    InterpreterStep.Result.Success
      (InstructionContext.map_interpreter sub
        {|
          InstructionContext.State.interpreter :=
            (interpreter
                <| Interpreter.bytecode :=
                  IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode)
                    .(Jumps.relative_jump)
                    interpreter.(Interpreter.bytecode)
                    {| Integer.value := 1 |}
                |>)
              <| Interpreter.gas := gas |>;
          InstructionContext.State.host := host;
        |}).
  Proof.
    eapply step_result_success
      with
        (opcode := {| Integer.value := 3 |})
        (instruction := instruction)
        (static_gas := {| Integer.value := 3 |});
      try eassumption.
    intros state.
    apply simple_sub.
  Qed.

  Lemma step_result_mul
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (IInterpreterTypes : InterpreterTypes.C WIRE_types)
      (table :
        array.t
          (Instruction.t WIRE H WIRE_types)
          {| Integer.value := 256 |})
      (interpreter : Interpreter.t WIRE WIRE_types)
      (host : H)
      (instruction : Instruction.t WIRE H WIRE_types)
      (gas : Gas.t)
      (H_opcode :
        IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode)
          .(Jumps.opcode) interpreter.(Interpreter.bytecode) =
        {| Integer.value := 2 |})
      (H_instruction :
        InterpreterStep.instruction_at table {| Integer.value := 2 |} =
        Some instruction)
      (H_gas :
        InterpreterStep.instruction_static_gas instruction =
        {| Integer.value := 5 |})
      (H_charge :
        Impl_Gas.record_cost
          interpreter.(Interpreter.gas)
          {| Integer.value := 5 |} =
        Some gas) :
    step_result_simple IInterpreterTypes table
      {|
        InstructionContext.State.interpreter := interpreter;
        InstructionContext.State.host := host;
      |} =
    InterpreterStep.Result.Success
      (InstructionContext.map_interpreter mul
        {|
          InstructionContext.State.interpreter :=
            (interpreter
                <| Interpreter.bytecode :=
                  IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode)
                    .(Jumps.relative_jump)
                    interpreter.(Interpreter.bytecode)
                    {| Integer.value := 1 |}
                |>)
              <| Interpreter.gas := gas |>;
          InstructionContext.State.host := host;
        |}).
  Proof.
    eapply step_result_success
      with
        (opcode := {| Integer.value := 2 |})
        (instruction := instruction)
        (static_gas := {| Integer.value := 5 |});
      try eassumption.
    intros state.
    apply simple_mul.
  Qed.

  Lemma step_result_div
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (IInterpreterTypes : InterpreterTypes.C WIRE_types)
      (table :
        array.t
          (Instruction.t WIRE H WIRE_types)
          {| Integer.value := 256 |})
      (interpreter : Interpreter.t WIRE WIRE_types)
      (host : H)
      (instruction : Instruction.t WIRE H WIRE_types)
      (gas : Gas.t)
      (H_opcode :
        IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode)
          .(Jumps.opcode) interpreter.(Interpreter.bytecode) =
        {| Integer.value := 4 |})
      (H_instruction :
        InterpreterStep.instruction_at table {| Integer.value := 4 |} =
        Some instruction)
      (H_gas :
        InterpreterStep.instruction_static_gas instruction =
        {| Integer.value := 5 |})
      (H_charge :
        Impl_Gas.record_cost interpreter.(Interpreter.gas)
          {| Integer.value := 5 |} = Some gas) :
    step_result_simple IInterpreterTypes table
      {| InstructionContext.State.interpreter := interpreter;
         InstructionContext.State.host := host |} =
    InterpreterStep.Result.Success
      (InstructionContext.map_interpreter div
        {| InstructionContext.State.interpreter :=
             (interpreter
                <| Interpreter.bytecode :=
                     IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode)
                       .(Jumps.relative_jump) interpreter.(Interpreter.bytecode)
                       {| Integer.value := 1 |} |>)
               <| Interpreter.gas := gas |>;
           InstructionContext.State.host := host |}).
  Proof.
    eapply step_result_success
      with (opcode := {| Integer.value := 4 |})
           (instruction := instruction)
           (static_gas := {| Integer.value := 5 |});
      try eassumption.
    intros state.
    apply simple_div.
  Qed.

  Lemma step_result_out_of_gas
      {H WIRE : Set} `{Link H} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (IInterpreterTypes : InterpreterTypes.C WIRE_types)
      (table :
        array.t
          (Instruction.t WIRE H WIRE_types)
          {| Integer.value := 256 |})
      (interpreter : Interpreter.t WIRE WIRE_types)
      (host : H)
      (opcode : u8)
      (instruction : Instruction.t WIRE H WIRE_types)
      (H_opcode :
        IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode)
          .(Jumps.opcode) interpreter.(Interpreter.bytecode) =
        opcode)
      (H_instruction :
        InterpreterStep.instruction_at table opcode = Some instruction)
      (H_charge :
        Impl_Gas.record_cost
          interpreter.(Interpreter.gas)
          (InterpreterStep.instruction_static_gas instruction) =
        None) :
    step_result_simple IInterpreterTypes table
      {|
        InstructionContext.State.interpreter := interpreter;
        InstructionContext.State.host := host;
      |} =
    InterpreterStep.Result.OutOfGas
      {|
        InstructionContext.State.interpreter :=
          halt_oog
            (interpreter
              <| Interpreter.bytecode :=
                IInterpreterTypes.(InterpreterTypes.Jumps_for_Bytecode)
                  .(Jumps.relative_jump)
                  interpreter.(Interpreter.bytecode)
                  {| Integer.value := 1 |}
              |>);
        InstructionContext.State.host := host;
      |}.
  Proof.
    destruct interpreter.
    cbn in H_charge.
    unfold step_result_simple, InterpreterStep.step_result,
      InterpreterStep.prepare.
    rewrite H_opcode, H_instruction.
    cbn in H_charge |- *.
    rewrite H_charge.
    reflexivity.
  Qed.
End InterpreterDispatch.
