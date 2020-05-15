Require Import ProofWeb.

Variable Q: Prop.
Variable P: D -> Prop.
Variable i: D.

Hypothesis P1 : all x,(P(x) <-> Q).

Theorem c1n013 : (all x,P(x)) <-> Q.
Proof.
iff_i H1 H2.
iff_e1 (P(i)).
all_e (all x, (P(x) <-> Q)).	
exact P1.
all_e (all x, P(x)).
exact H1.
all_i a.
iff_e2 Q.
all_e (all x, (P(x) <-> Q)).
exact P1.
exact H2.
Qed.