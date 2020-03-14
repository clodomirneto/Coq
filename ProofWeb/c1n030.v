Require Import ProofWeb.

Variable P: D -> Prop.
Variable i: D.

Hypothesis P1 : all x,P(x). 

Theorem c1n030 : ~all x,~P(x).
Proof.
neg_i H1.
neg_e (P(i)).
all_e (all x, ~P(x)).
exact H1.
all_e (all x, P(x)).
exact P1.
Qed.