Require Import ProofWeb.

Variable P: D -> Prop.

Hypothesis P1 : all x,all x,P(x).

Theorem c1n036 : all x,P(x).
Proof.
all_e (all x, all x, P(x)).
exact P1.
Qed.