Require Import ProofWeb.

Variables A B : Prop.

Hypothesis P1 : A \/ B.
Hypothesis P2 : ~A.

Theorem sd: B.
Proof.
dis_e (A \/ B) Ha Hb.
exact P1.
PBC Hnb.
neg_e (A).
exact P2.
exact Ha.
exact Hb.
Qed.