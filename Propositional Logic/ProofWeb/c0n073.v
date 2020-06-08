Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (A \/ ~B).
Hypothesis P2: B.

Theorem c0n073 : A.
Proof.
PBC H1.
neg_e B.
dis_e (A \/ ~B) H2 H3.
exact P1.
neg_i H4.
neg_e A.
exact H1.
exact H2.
exact H3.
exact P2.
Qed.