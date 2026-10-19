Require Import alloy_primitives.links.aliases.
Require Import p256.simulate.arithmetic.field.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

(** Constants from p256/arithmetic.rs, specialized to NistP256. *)
Module NistP256.
  Definition EQUATION_A : FieldElement.t :=
    FieldElement.sub FieldElement.ZERO
      (FieldElement.add FieldElement.ONE
        (FieldElement.add FieldElement.ONE FieldElement.ONE)).

  Definition EQUATION_B : FieldElement.t :=
    {| FieldElement.repr := {| Uint.value :=
      41058363725152142129326129780047268409114441015993725554835256314039467401291 |} |}.

  Definition GENERATOR : FieldElement.t * FieldElement.t :=
    ({| FieldElement.repr := {| Uint.value :=
        48439561293906451759052585252797914202762949526041747995844080717082404635286 |} |},
     {| FieldElement.repr := {| Uint.value :=
        36134250956749795798585127919587881956611106672985015071877198253568414405109 |} |}).
End NistP256.
