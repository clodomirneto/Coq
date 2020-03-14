Require Import ProofWeb.

Variable P : D -> Prop.

Hypothesis P1 : all x,all y,(P(x) /\ P(y)).

Theorem c1n041 : all x,P(x).
Proof.
all_i a.
con_e1 (P(a)).
all_e (all y, (P(a) /\ P(y))).
all_e (all x, all y, (P(x) /\ P(y))).
exact P1.
Qed.