Require Import ProofWeb.

Variables P : D -> Prop.

Hypothesis P1 : all x,all y,(P(x) \/ P(y)).

Theorem c1n042 : all x,P(x).
Proof.
all_i a.
dis_e (P(a) \/ P(a)) H1 H2.
all_e (all y, (P(a) \/ P(y))).
all_e (all x, all y, (P(x) \/ P(y))).
exact P1.
exact H1.
exact H2.
Qed.