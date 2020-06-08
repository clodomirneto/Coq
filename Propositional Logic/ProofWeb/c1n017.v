Require Import ProofWeb.

Variables P Q: D -> Prop.

Hypothesis P1 : all x,(P(x) /\ Q(x)). 

Theorem c1n017 : all y,(Q(y) /\ P(y)).
Proof.
all_i a.
con_i.
con_e2 (P(a)).
all_e (all x, (P(x) /\ Q(x))).
exact P1.
con_e1 (Q(a)).
all_e (all x, (P(x) /\ Q(x))).
exact P1.
Qed.