Require Import ProofWeb.

Variables R : D -> Prop.

Hypothesis P1 : exi x,R(x).

Theorem c1n055 : ~all x,~R(x).
Proof.
exi_e (exi x, R(x)) a H1.
exact P1.
neg_i H2.
neg_e (R(a)).
all_e (all x, ~R(x)).
exact H2.
exact H1.
Qed.