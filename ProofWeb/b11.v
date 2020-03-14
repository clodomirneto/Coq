Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1 : ~A.

Hypothesis P2 : A \/ B.

Theorem b11 : B.

Proof.
dis_e (A \/ B) H1 H2.
exact P2.
PBC H3.
neg_e (A).
exact P1.
exact H1.
exact H2.
Qed.
