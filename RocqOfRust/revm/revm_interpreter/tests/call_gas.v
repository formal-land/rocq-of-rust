Require Import revm.revm_interpreter.gas.simulate.calc.
Require Import revm.revm_primitives.links.hardfork.
Require Import simulate.RocqOfRust.

Module Test.
  Lemma frontier_call_base :
    calc_call_static_gas SpecId.FRONTIER false = 40.
  Proof. vm_compute. reflexivity. Qed.

  Lemma homestead_call_base :
    calc_call_static_gas SpecId.HOMESTEAD false = 40.
  Proof. vm_compute. reflexivity. Qed.

  Lemma tangerine_call_base :
    calc_call_static_gas SpecId.TANGERINE false = 700.
  Proof. vm_compute. reflexivity. Qed.

  Lemma istanbul_call_base :
    calc_call_static_gas SpecId.ISTANBUL false = 700.
  Proof. vm_compute. reflexivity. Qed.

  Lemma berlin_call_base :
    calc_call_static_gas SpecId.BERLIN false = 100.
  Proof. vm_compute. reflexivity. Qed.

  Lemma cancun_call_base :
    calc_call_static_gas SpecId.CANCUN false = 100.
  Proof. vm_compute. reflexivity. Qed.

  Lemma prague_call_base :
    calc_call_static_gas SpecId.PRAGUE false = 100.
  Proof. vm_compute. reflexivity. Qed.

  Lemma frontier_value_transfer :
    calc_call_static_gas SpecId.FRONTIER true = 9040.
  Proof. vm_compute. reflexivity. Qed.

  Lemma tangerine_value_transfer :
    calc_call_static_gas SpecId.TANGERINE true = 9700.
  Proof. vm_compute. reflexivity. Qed.

  Lemma berlin_value_transfer :
    calc_call_static_gas SpecId.BERLIN true = 9100.
  Proof. vm_compute. reflexivity. Qed.

  Lemma prague_value_transfer :
    calc_call_static_gas SpecId.PRAGUE true = 9100.
  Proof. vm_compute. reflexivity. Qed.
End Test.
