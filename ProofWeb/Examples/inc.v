Require Import ProofWeb.

Variables A B : Prop.

Hypothesis P1 : A.
Hypothesis P2 : ~A.

Theorem inc : B.
Proof.
PBC Hnb.
neg_e (A).
exact P2.
exact P1.
Qed.