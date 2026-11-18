From Stdlib Require Export ZArith List String.
Export ListNotations.
Open Scope Z_scope.

Inductive phase := Entry | Current | Expiry.
Record observations := {
  word_at : phase -> list string -> Z;
  slice_at : phase -> list string -> list Z
}.

Inductive term :=
| Number (n : Z)
| Bound (index : nat)
| Word (at_time : phase) (path : list string)
| Length (at_time : phase) (path : list string)
| Index (at_time : phase) (path : list string) (at_index : term)
| Plus (x y : term)
| Minus (x y : term).

Definition lookup (xs : list Z) (i : Z) : option Z :=
  if i <? 0 then None else nth_error xs (Z.to_nat i).

Fixpoint value (o : observations) (locals : list Z) (t : term) : option Z :=
  match t with
  | Number n => Some n
  | Bound i => nth_error locals i
  | Word p k => Some (word_at o p k)
  | Length p k => Some (Z.of_nat (List.length (slice_at o p k)))
  | Index p k i =>
      match value o locals i with Some j => lookup (slice_at o p k) j | None => None end
  | Plus x y | Minus x y =>
      match value o locals x, value o locals y with
      | Some a, Some b => Some (match t with Plus _ _ => a+b | _ => a-b end)
      | _, _ => None
      end
  end.

Inductive comparison := Equal | Less | AtMost.
Inductive formula :=
| Truth
| Compare (op : comparison) (a b : term)
| Both (a b : formula)
| Implies (a b : formula)
| ForallInt (body : formula).

Fixpoint holds (o : observations) (locals : list Z) (f : formula) : Prop :=
  match f with
  | Truth => True
  | Compare op a b =>
      match value o locals a, value o locals b with
      | Some x, Some y => match op with Equal => x = y | Less => x < y | AtMost => x <= y end
      | _, _ => False
      end
  | Both a b => holds o locals a /\ holds o locals b
  | Implies a b => holds o locals a -> holds o locals b
  | ForallInt body => forall z : Z, holds o (z :: locals) body
  end.

(** The execution link enumerates every observation it implements. Replay checks
    this footprint so a default arm in a hand-written view cannot prove a claim. *)
Inductive access := WordPath (p : phase) (path : list string)
                  | SlicePath (p : phase) (path : list string).
Definition phase_eq_dec (a b : phase) : {a=b}+{a<>b}.
Proof. decide equality. Defined.
Definition access_eq_dec (a b : access) : {a=b}+{a<>b}.
Proof. decide equality; first [apply phase_eq_dec | apply list_eq_dec, string_dec]. Defined.
Fixpoint term_reads (t : term) : list access :=
  match t with
  | Number _ | Bound _ => []
  | Word p k => [WordPath p k]
  | Length p k => [SlicePath p k]
  | Index p k i => SlicePath p k :: term_reads i
  | Plus a b | Minus a b => term_reads a ++ term_reads b
  end.
Fixpoint reads (f : formula) : list access :=
  match f with
  | Truth => []
  | Compare _ a b => term_reads a ++ term_reads b
  | Both a b | Implies a b => reads a ++ reads b
  | ForallInt b => reads b
  end.
Definition covered (allowed : list access) (f : formula) : bool :=
  forallb (fun a => if in_dec access_eq_dec a allowed then true else false) (reads f).
