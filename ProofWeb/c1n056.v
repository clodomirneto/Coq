Require Import ProofWeb.

Variables R : D -> Prop.

Hypothesis P1 : exi x,~R(x).

Theorem c1n056 : ~all x,R(x).
Proof.
exi_e (exi x, ~R(x)) a H1.
exact P1.
neg_i H2.
neg_e (all x, R(x)).
neg_i H3.
neg_e (R(a)).
exact H1.
all_e (all x, R(x)).
exact H3.
exact H2.
Qed.