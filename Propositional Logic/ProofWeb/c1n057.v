Require Import ProofWeb.

Variable R : D -> Prop.

Hypothesis P1 : all x,~R(x) .

Theorem c1n057 : ~exi x,R(x).
Proof.
neg_i H1.
neg_e (all x, ~R(x)).
exi_e (exi x, R(x)) a H2.
exact H1.
neg_i H3.
neg_e (R(a)).
all_e (all x, ~R(x)).
exact P1.
exact H2.
exact P1.
Qed.