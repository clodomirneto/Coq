Require Import ProofWeb.

Variable P: D -> Prop.
Variable i: D.

Hypothesis P1 : all x,P(x). 

Theorem c1n029 : exi y,P(y).
Proof.
exi_i i.
all_e (all x, P(x)).
exact P1.
Qed.