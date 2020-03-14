Require Import ProofWeb.

Variable P: D -> Prop.

Hypothesis P1 : all x,P(x).

Theorem c1n038 : all x,all y,(P(x) /\ P(y)).
Proof.
all_i a.
all_i b.
con_i.
all_e (all x, P(x)).
exact P1.
all_e (all x, P(x)).
exact P1.
Qed.