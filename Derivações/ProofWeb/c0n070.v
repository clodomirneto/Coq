Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (A \/ B).
Hypothesis P2: ~A.

Theorem c0n070 : B.
Proof.
PBC H1.
neg_e A.
exact P2.
dis_e (A \/ B) H2 H3.
exact P1.
exact H2.
PBC H4.
neg_e B.
exact H1.
exact H3.
Qed.