Require Import ProofWeb.

Variable P: D -> Prop.

Hypothesis P1 : all x,P(x).

Theorem c1n037 : all x,all y,(P(x) \/ P(y)).
Proof.
all_i a.
all_i b.
dis_i1.
all_e (all x, P(x)).
exact P1.
Qed.