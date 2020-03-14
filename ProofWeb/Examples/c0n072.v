Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (A \/ B).
Hypothesis P2: ~B.

Theorem c0n072 : A.
Proof.
PBC H1.
neg_e B.
exact P2.
dis_e (A \/ B) H2 H3.
exact P1.
PBC H4.
neg_e A.
exact H1.
exact H2.
PBC H5.
neg_e B.
exact P2.
exact H3.
Qed.