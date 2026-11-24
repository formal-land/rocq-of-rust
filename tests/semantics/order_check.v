Require Import RocqOfRust.simulate.RocqOfRust ReleaseTests.order.
Definition bytev (z:Z) : u8 := {|Integer.value := z|}.
Instance run_simple : Run.Trait simple_order [] [] [] u8.
Proof. constructor. run_symbolic. Defined.
Instance run_primitive : Run.Trait primitive_order [] [] [] u8.
Proof. constructor. run_symbolic. Defined.
Example simple_order_eq :
 {{ SimulateM.eval_f run_simple []%stack 🌲 (Output.Success (bytev 0), []%stack) }}.
Proof. repeat s. Qed.
Example primitive_order_eq :
 {{ SimulateM.eval_f run_primitive []%stack 🌲 (Output.Success (bytev 10), []%stack) }}.
Proof. repeat s. Qed.

Instance run_early : Run.Trait early_rhs [] [] [] u8.
Proof. constructor. run_symbolic. Defined.
Example rhs_returns_first :
 {{ SimulateM.eval_f run_early []%stack 🌲 (Output.Success (bytev 5), []%stack) }}.
Proof. repeat s. Qed.

Module Counter.
  RocqOfRustLinkTupleStruct "order::Counter" := { count : u8 }.
End Counter.
Export (hints) Counter.
Module AddAssign := Impl_core_ops_arith_AddAssign_u8_for_order_Counter.
Instance counter_method : IsTraitMethod.C
  {| TraitHeader.trait_name := "core::ops::arith::AddAssign";
     TraitHeader.self_ty := Φ Counter.t; TraitHeader.trait_consts := [];
     TraitHeader.trait_tys := [Φ u8] |} "add_assign" AddAssign.add_assign.
Proof. constructor. eapply IsTraitMethod.Defined; [exact AddAssign.Implements | reflexivity]. Qed.
Instance run_counter (c : '&mut Counter.t) (v : u8) :
  Run.Trait AddAssign.add_assign [] [] [φ c; φ v] unit.
Proof. constructor. run_symbolic. Defined.
Instance run_overload : Run.Trait overload [] [] [] u8.
Proof. constructor. run_symbolic. Defined.
Example overloaded_assignment_borrows_first :
 {{ SimulateM.eval_f run_overload []%stack 🌲 (Output.Success (bytev 1), []%stack) }}.
Proof. repeat s. Qed.
