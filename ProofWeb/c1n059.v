Require Import ProofWeb.

Variable R : D -> Prop.

Hypothesis P1 : ~exi x,~R(x) .

Theorem c1n059 : all x,R(x).
Proof.
all_i a.
PBC H1.
neg_e (exi x, ~R(x)).
exact P1.
exi_i a.
exact H1.
Qed.