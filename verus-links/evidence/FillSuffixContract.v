Require Export Assertion.
Import ListNotations.
Open Scope string_scope.
Definition target_function := "fill::fill_prefix".
Definition target_site := "ensures_2".
Definition requires_0 := (Compare AtMost (Word Current ["n"]) (Length Entry ["xs"])).
Definition ensures_0 := (Compare Equal (Length Expiry ["xs"]) (Length Entry ["xs"])).
Definition ensures_1 := (ForallInt (Implies (Both (Compare AtMost (Number (0)) (Bound 0%nat)) (Compare Less (Bound 0%nat) (Word Current ["n"]))) (Compare Equal (Index Expiry ["xs"] (Bound 0%nat)) (Word Current ["value"])))).
Definition ensures_2 := (ForallInt (Implies (Both (Compare AtMost (Word Current ["n"]) (Bound 0%nat)) (Compare Less (Bound 0%nat) (Length Entry ["xs"]))) (Compare Equal (Index Expiry ["xs"] (Bound 0%nat)) (Index Entry ["xs"] (Bound 0%nat))))).
Definition invariant_0 := (Both (Compare AtMost (Word Current ["i"]) (Word Current ["n"])) (Compare AtMost (Word Current ["n"]) (Length Current ["xs"]))).
Definition invariant_1 := (Compare Equal (Length Current ["xs"]) (Length Entry ["xs"])).
Definition invariant_2 := (ForallInt (Implies (Both (Compare AtMost (Number (0)) (Bound 0%nat)) (Compare Less (Bound 0%nat) (Word Current ["i"]))) (Compare Equal (Index Current ["xs"] (Bound 0%nat)) (Word Current ["value"])))).
Definition contract_post (o : observations) := holds o [] (Both ensures_0 (Both ensures_1 ensures_2)).
Definition pre_syntax := requires_0.
Definition post_syntax := ensures_2.
Definition pre (o : observations) := holds o [] pre_syntax.
Definition post (o : observations) := holds o [] post_syntax.
