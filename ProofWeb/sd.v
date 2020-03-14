Require Import ProofWeb.

Parameter A B: Prop.

Hypothesis P1: A \/ B.
Hypothesis P2: ~A.

Theorem sd: B.
Proof.
dis_e (A \/ B) H1 H2.
exact P1.
PBC H3.
neg_e A.
exact P2.
exact H1.
exact H2.
Qed.