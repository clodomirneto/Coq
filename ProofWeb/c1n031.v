Require Import ProofWeb.

Variable P: D -> Prop.
Variable i: D.

Hypothesis P1 : P(i). 

Theorem c1n031 : ~all x,~P(x).
Proof.
neg_i H1.
neg_e (P(i)).
all_e (all x, ~P(x)).
exact H1.
exact P1.
Qed.