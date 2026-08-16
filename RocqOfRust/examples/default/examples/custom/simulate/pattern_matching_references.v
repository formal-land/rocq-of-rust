Require Import simulate.RocqOfRust.
Require Import examples.default.examples.custom.links.pattern_matching_references.

Definition match_value (value : u32) : u32 :=
  value.

Lemma match_value_eq (value : u32) :
  {{
    SimulateM.eval_f (run_match_value value) []%stack 🌲
    (Output.Success (match_value value), []%stack)
  }}.
Proof.
  s.
Qed.

Definition match_ref (value : u32) : u32 :=
  value.

Lemma match_ref_eq (value : u32) :
  {{
    SimulateM.eval_f (run_match_ref value) []%stack 🌲
    (Output.Success (match_ref value), []%stack)
  }}.
Proof.
  s.
Qed.

Definition match_ref_mut (value : u32) : u32 :=
  value +i 1.

Lemma match_ref_mut_eq (value : u32) :
  let ref_value : '&mut u32 := make_ref 0 in
  {{
    SimulateM.eval_f (run_match_ref_mut ref_value) [value]%stack 🌲
    (Output.Success (match_ref_mut value), [match_ref_mut value]%stack)
  }}.
Proof.
  s.
Qed.

Definition match_reference (value : u32) : u32 :=
  value.

Lemma match_reference_eq (value : u32) :
  let ref_value : '& u32 := make_ref 0 in
  {{
    SimulateM.eval_f (run_match_reference ref_value) [value]%stack 🌲
    (Output.Success (match_reference value), [value]%stack)
  }}.
Proof.
  s.
Qed.

Definition match_mutable_reference (value : u32) : u32 :=
  value.

Lemma match_mutable_reference_eq (value : u32) :
  let ref_value : '&mut u32 := make_ref 0 in
  {{
    SimulateM.eval_f (run_match_mutable_reference ref_value) [value]%stack 🌲
    (Output.Success (match_mutable_reference value), [value]%stack)
  }}.
Proof.
  s.
Qed.

Example match_value_five :
  match_value {| Integer.value := 5 |} = {| Integer.value := 5 |}.
Proof. reflexivity. Qed.

Example match_ref_five :
  match_ref {| Integer.value := 5 |} = {| Integer.value := 5 |}.
Proof. reflexivity. Qed.

Example match_ref_mut_five :
  match_ref_mut {| Integer.value := 5 |} = {| Integer.value := 6 |}.
Proof. reflexivity. Qed.

Example match_reference_five :
  match_reference {| Integer.value := 5 |} = {| Integer.value := 5 |}.
Proof. reflexivity. Qed.

Example match_mutable_reference_five :
  match_mutable_reference {| Integer.value := 5 |} = {| Integer.value := 5 |}.
Proof. reflexivity. Qed.
