Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulate.M.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.arithmetic.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.simulate.add.
Require Import ruint.simulate.cmp.
Require Import ruint.simulate.div.
Require Import ruint.simulate.mul.

Lemma add_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_add run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        gas_macro interpreter constants.VERYLOW id (fun interpreter =>
        popn_top_macro interpreter {| Integer.value := 1 |} id (fun arr top interpreter =>
          let '{| ArrayPair.x := op1 |} := arr.(array.value) in
          let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
          let stack :=
            top.(RefStub.injection)
              interpreter.(Interpreter.stack) (Impl_Uint.wrapping_add op1 op2) in
          interpreter
            <| Interpreter.stack := stack |>
        ));
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  destruct InterpreterTypesEq as [[] [] [] []].
  cbn.
  gas_macro_eq H gas set_instruction_result.
  popn_top_macro_eq H IInterpreterTypes popn_top set_instruction_result.
  get_can_access.
  eapply Run.Call. {
    apply Impl_Uint.wrapping_add_eq.
  }
  get_can_access.
  apply Run.Pure.
Qed.

Lemma mul_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_mul run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        gas_macro interpreter constants.LOW id (fun interpreter =>
        popn_top_macro interpreter {| Integer.value := 1 |} id (fun arr top interpreter =>
          let '{| ArrayPair.x := op1 |} := arr.(array.value) in
          let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
          let stack :=
            top.(RefStub.injection)
              interpreter.(Interpreter.stack) (Impl_Uint.wrapping_mul op1 op2) in
          interpreter
            <| Interpreter.stack := stack |>
        ));
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  destruct InterpreterTypesEq as [[] [] [] []].
  cbn.
  gas_macro_eq H gas set_instruction_result.
  popn_top_macro_eq H IInterpreterTypes popn_top set_instruction_result.
  get_can_access.
  eapply Run.Call. {
    apply Impl_Uint.wrapping_mul_eq.
  }
  get_can_access.
  apply Run.Pure.
Qed.

Lemma sub_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_sub run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        gas_macro interpreter constants.VERYLOW id (fun interpreter =>
        popn_top_macro interpreter {| Integer.value := 1 |} id (fun arr top interpreter =>
          let '{| ArrayPair.x := op1 |} := arr.(array.value) in
          let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
          let stack :=
            top.(RefStub.injection)
              interpreter.(Interpreter.stack) (Impl_Uint.wrapping_sub op1 op2) in
          interpreter
            <| Interpreter.stack := stack |>
        ));
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  destruct InterpreterTypesEq as [[] [] [] []].
  cbn.
  gas_macro_eq H gas set_instruction_result.
  popn_top_macro_eq H IInterpreterTypes popn_top set_instruction_result.
  get_can_access.
  eapply Run.Call. {
    apply Impl_Uint.wrapping_sub_eq.
  }
  get_can_access.
  apply Run.Pure.
Qed.

Lemma div_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_div run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        gas_macro interpreter constants.LOW id (fun interpreter =>
        popn_top_macro interpreter {| Integer.value := 1 |} id (fun arr top interpreter =>
          let '{| ArrayPair.x := op1 |} := arr.(array.value) in
          let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
          if Impl_Uint.is_zero op2 then
            interpreter
          else
            let stack :=
              top.(RefStub.injection)
                interpreter.(Interpreter.stack)
                (Impl_Uint.wrapping_div op1 op2) in
            interpreter
              <| Interpreter.stack := stack |>
        ));
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  destruct InterpreterTypesEq as [[] [] [] []].
  cbn.
  gas_macro_eq H gas set_instruction_result.
  popn_top_macro_eq H IInterpreterTypes popn_top set_instruction_result.
  cbn.
  eapply Run.Call; cbn. {
    setoid_rewrite (
      Impl_Uint.is_zero_like
        _
        (BITS := {| Integer.value := 256 |})
        (LIMBS := {| Integer.value := 4 |})
    ).
    cbn.
    get_can_access.
    apply Run.Pure.
  }
  cbn.
  eapply Run.Call; cbn. {
    apply Run.Pure.
  }
  cbn.
  eapply Run.Call; cbn. {
    apply Run.Pure.
  }
  cbn.
  destruct Impl_Uint.is_zero; cbn.
  { apply Run.Pure. }
  { progress repeat get_can_access.
    eapply Run.Call; cbn. {
      apply Impl_Uint.wrapping_div_eq.
    }
    cbn.
    progress repeat get_can_access.
    apply Run.Pure.
  }
Qed.

Global Opaque run_div.

Lemma sdiv_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :

  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_sdiv run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        gas_macro interpreter constants.LOW (fun interpreter =>
        popn_top_macro interpreter {| Integer.value := 1 |}
          (fun arr top interpreter =>
            let '{| ArrayPair.x := op1 |} := arr.(array.value) in
            let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
            if Impl_Uint.is_zero op2 then
              interpreter
            else
              let stack :=
                top.(RefStub.injection)
                  interpreter.(Interpreter.stack)
                  (Impl_Uint.wrapping_sdiv op1 op2) in
              interpreter <| Interpreter.stack := stack |>
          ));
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  destruct InterpreterTypesEq as [[] []].
  cbn.
  gas_macro_eq H gas set_instruction_result.
  popn_top_macro_eq H IInterpreterTypes popn_top set_instruction_result.
  cbn.
  destruct Impl_Uint.is_zero; cbn.
  { apply Run.Pure. }
  { repeat get_can_access.
    eapply Run.Call; cbn.
    { apply Impl_Uint.wrapping_sdiv_eq. }
    repeat get_can_access.
    apply Run.Pure.
  }
Qed.
Global Opaque run_sdiv.

Lemma rem_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :

  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_rem run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        gas_macro interpreter constants.LOW (fun interpreter =>
        popn_top_macro interpreter {| Integer.value := 1 |}
          (fun arr top interpreter =>
            let '{| ArrayPair.x := op1 |} := arr.(array.value) in
            let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
            if Impl_Uint.is_zero op2 then
              interpreter
            else
              let stack :=
                top.(RefStub.injection)
                  interpreter.(Interpreter.stack)
                  (Impl_Uint.wrapping_rem op1 op2) in
              interpreter <| Interpreter.stack := stack |>
          ));
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  destruct InterpreterTypesEq as [[] []].
  cbn.
  gas_macro_eq H gas set_instruction_result.
  popn_top_macro_eq H IInterpreterTypes popn_top set_instruction_result.
  cbn.
  destruct Impl_Uint.is_zero; cbn.
  { apply Run.Pure. }
  { repeat get_can_access.
    eapply Run.Call; cbn.
    { apply Impl_Uint.wrapping_rem_eq. }
    repeat get_can_access.
    apply Run.Pure.
  }
Qed.
Global Opaque run_rem.

Lemma rem_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :

  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_rem run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        gas_macro interpreter constants.LOW (fun interpreter =>
        popn_top_macro interpreter {| Integer.value := 1 |}
          (fun arr top interpreter =>
            let '{| ArrayPair.x := op1 |} := arr.(array.value) in
            let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
            if Impl_Uint.is_zero op2 then
              interpreter
            else
              let stack :=
                top.(RefStub.injection)
                  interpreter.(Interpreter.stack)
                  (Impl_Uint.wrapping_rem op1 op2) in
              interpreter <| Interpreter.stack := stack |>
          ));
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  destruct InterpreterTypesEq as [[] []].
  cbn.
  gas_macro_eq H gas set_instruction_result.
  popn_top_macro_eq H IInterpreterTypes popn_top set_instruction_result.
  cbn.
  destruct Impl_Uint.is_zero; cbn.
  { apply Run.Pure. }
  { repeat get_can_access.
    eapply Run.Call; cbn.
    { apply Impl_Uint.wrapping_rem_eq. }
    repeat get_can_access.
    apply Run.Pure.
  }
Qed.
Global Opaque run_rem.

Lemma smod_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :

  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_smod run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        gas_macro interpreter constants.LOW (fun interpreter =>
        popn_top_macro interpreter {| Integer.value := 1 |}
          (fun arr top interpreter =>
            let '{| ArrayPair.x := op1 |} := arr.(array.value) in
            let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
            if Impl_Uint.is_zero op2 then
              interpreter
            else
              let stack :=
                top.(RefStub.injection)
                  interpreter.(Interpreter.stack)
                  (Impl_Uint.wrapping_smod op1 op2) in
              interpreter <| Interpreter.stack := stack |>
          ));
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  destruct InterpreterTypesEq as [[] []].
  cbn.
  gas_macro_eq H gas set_instruction_result.
  popn_top_macro_eq H IInterpreterTypes popn_top set_instruction_result.
  cbn.
  destruct Impl_Uint.is_zero; cbn.
  { apply Run.Pure. }
  { repeat get_can_access.
    eapply Run.Call; cbn.
    { apply Impl_Uint.wrapping_smod_eq. }
    repeat get_can_access.
    apply Run.Pure.
  }
Qed.
Global Opaque run_smod.

Lemma addmod_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :

  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_addmod run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        gas_macro interpreter constants.MID (fun interpreter =>
        popn_top_macro interpreter {| Integer.value := 2 |}
          (fun arr top interpreter =>
            let '{| ArrayTriple.x := a; y := b |} := arr.(array.value) in
            let m := top.(RefStub.projection) interpreter.(Interpreter.stack) in
            if Impl_Uint.is_zero m then
              interpreter
            else
              let stack :=
                top.(RefStub.injection)
                  interpreter.(Interpreter.stack)
                  (Impl_Uint.addmod a b m) in
              interpreter <| Interpreter.stack := stack |>
          ));
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  destruct InterpreterTypesEq as [[] []].
  cbn.
  gas_macro_eq H gas set_instruction_result.
  popn_top_macro_eq H IInterpreterTypes popn_top set_instruction_result.
  cbn.
  destruct Impl_Uint.is_zero; cbn.
  { apply Run.Pure. }
  { repeat get_can_access.
    eapply Run.Call; cbn.
    { apply Impl_Uint.addmod_eq. }
    repeat get_can_access.
    apply Run.Pure.
  }
Qed.
Global Opaque run_addmod.

Lemma mulmod_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :

  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_mulmod run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [
        gas_macro interpreter constants.MID (fun interpreter =>
        popn_top_macro interpreter {| Integer.value := 2 |}
          (fun arr top interpreter =>
            let '{| ArrayTriple.x := a; y := b |} := arr.(array.value) in
            let m := top.(RefStub.projection) interpreter.(Interpreter.stack) in
            if Impl_Uint.is_zero m then
              interpreter
            else
              let stack :=
                top.(RefStub.injection)
                  interpreter.(Interpreter.stack)
                  (Impl_Uint.mulmod a b m) in
              interpreter <| Interpreter.stack := stack |>
          ));
        _host
      ]%stack
    )
  }}.
Proof.
  intros.
  destruct InterpreterTypesEq as [[] []].
  cbn.
  gas_macro_eq H gas set_instruction_result.
  popn_top_macro_eq H IInterpreterTypes popn_top set_instruction_result.
  cbn.
  destruct Impl_Uint.is_zero; cbn.
  { apply Run.Pure. }
  { repeat get_can_access.
    eapply Run.Call; cbn.
    { apply Impl_Uint.mulmod_eq. }
    repeat get_can_access.
    apply Run.Pure.
  }
Qed.
Global Opaque run_mulmod.
