Require Import ProofWeb.

Variable P: D -> Prop.

Hypothesis P1 : all x,P(x).

Theorem c1n033 : all y,P(y).
Proof.
all_i a.
all_e (all x, P(x)).
exact P1.
Qed.