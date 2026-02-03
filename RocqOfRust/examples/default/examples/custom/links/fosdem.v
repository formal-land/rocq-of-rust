Require Import links.RocqOfRust.
Require Import examples.default.examples.custom.fosdem.

(*
struct Counter {
  value: u64,
}
*)
Module Counter.
  Record t : Set := {
    value : u64;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "fosdem::Counter";
    φ x :=
      Value.StructRecord "fosdem::Counter" [] [] [
        ("value", φ x.(value))
      ];
  }.

  Definition of_ty : OfTy.t (Ty.path "fosdem::Counter").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with value value' :
    value' = φ value ->
    Value.StructRecord "fosdem::Counter" [] [] [
      ("value", value')
    ] = φ (Build_t value).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value (value : u64) value' :
    value' = φ value ->
    OfValue.t (
      Value.StructRecord "fosdem::Counter" [] [] [
        ("value", value')
      ]
    ).
  Proof.
    intros.
    eapply OfValue.Make with (A := t).
    apply of_value_with; eassumption.
  Defined.
  Smpl Add eapply of_value : of_value.

  Module SubPointer.
    Definition get_value : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "fosdem::Counter" "value") :=
    {|
      SubPointer.Runner.projection x := Some x.(value);
      SubPointer.Runner.injection x y := Some (x <| value := y |>);
    |}.

    Lemma get_value_is_valid :
      SubPointer.Runner.Valid.t get_value.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_value_is_valid : run_sub_pointer.
  End SubPointer.
End Counter.

(* const MAX_VALUE: u64 = 1000 *)
Instance run_MAX_VALUE :
  Run.Trait value_MAX_VALUE [] [] [] ('* u64).
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_MAX_VALUE.

(* impl Counter { fn increment(&mut self, amount: u64) } *)
Instance run_increment (self : '&mut Counter.t) (amount : u64) :
  Run.Trait Impl_fosdem_Counter.increment [] [] [φ self; φ amount] unit.
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_increment.
