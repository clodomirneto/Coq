Require Import ProofWeb.

Variable R : D -> Prop.

Hypothesis P1 : ~all x,~R(x).

Theorem c1n060 : exi x,R(x).
Proof.
PBC H1.
neg_e (all x, ~R(x)).
exact P1.
all_i a.
neg_i H2.
neg_e (exi x, R(x)).
exact H1.
exi_i a.
exact H2.
Qed.