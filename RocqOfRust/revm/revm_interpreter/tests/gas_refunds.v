Require Import simulate.RocqOfRust.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.simulate.gas.

Module Test.
  Definition gas_with_refund (limit remaining : u64) (refund : i64) : Gas.t :=
    (Impl_Gas.new limit)
      <| Gas.remaining := remaining |>
      <| Gas.refunded := refund |>.

  Lemma negative_refund_cast_before_cap :
    i[(Impl_Gas.set_final_refund (gas_with_refund 100 0 (-1)) true).(Gas.refunded)] = 20.
  Proof. vm_compute. reflexivity. Qed.

  Lemma pre_london_refund_cap :
    i[(Impl_Gas.set_final_refund (gas_with_refund 100 0 90) false).(Gas.refunded)] = 50.
  Proof. vm_compute. reflexivity. Qed.

  Lemma london_refund_cap :
    i[(Impl_Gas.set_final_refund (gas_with_refund 100 0 90) true).(Gas.refunded)] = 20.
  Proof. vm_compute. reflexivity. Qed.

  Lemma refund_below_cap :
    i[(Impl_Gas.set_final_refund (gas_with_refund 100 0 19) true).(Gas.refunded)] = 19.
  Proof. vm_compute. reflexivity. Qed.

  Lemma refund_uses_spent_gas :
    i[(Impl_Gas.set_final_refund (gas_with_refund 100 50 90) true).(Gas.refunded)] = 10.
  Proof. vm_compute. reflexivity. Qed.

  Lemma maximum_limit_refund :
    i[(Impl_Gas.set_final_refund (gas_with_refund (2 ^ 64 - 1) 0 (-1)) false).(Gas.refunded)] = (2 ^ 63 - 1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma used_saturates :
    i[Impl_Gas.used (gas_with_refund 100 90 11)] = 0.
  Proof. vm_compute. reflexivity. Qed.

  Lemma used_negative_refund_cast :
    i[Impl_Gas.used (gas_with_refund 100 90 (-1))] = 0.
  Proof. vm_compute. reflexivity. Qed.

  Lemma used_subtracts_refund :
    i[Impl_Gas.used (gas_with_refund 100 20 10)] = 70.
  Proof. vm_compute. reflexivity. Qed.

  Lemma spent_sub_refunded_saturates :
    i[Impl_Gas.spent_sub_refunded (gas_with_refund 100 90 11)] = 0.
  Proof. vm_compute. reflexivity. Qed.

  Lemma set_spent_over_limit :
    i[(Impl_Gas.set_spent (gas_with_refund 100 90 7) 101).(Gas.remaining)] = 0.
  Proof. vm_compute. reflexivity. Qed.

  Lemma set_spent_preserves_refund :
    i[(Impl_Gas.set_spent (gas_with_refund 100 90 7) 20).(Gas.refunded)] = 7.
  Proof. vm_compute. reflexivity. Qed.

End Test.
