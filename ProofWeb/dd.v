Require Import ProofWeb.

Parameter A B C D: Prop.

Hypothesis P1: ~C \/ ~D.
Hypothesis P2: A -> C.
Hypothesis P3: B -> D.

Theorem dd: ~A \/ ~B.
Proof.
dis_e (~C \/ ~D) H1 H2.
exact P1.
dis_i1.
neg_i H3.
neg_e C.
exact H1.
imp_e A.
exact P2.
exact H3.
dis_i2.
neg_i H4.
neg_e D.
exact H2.
imp_e B.
exact P3.
exact H4.
Qed.