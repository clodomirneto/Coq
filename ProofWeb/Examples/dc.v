Require Import ProofWeb.

Parameter A B C D: Prop.

Hypothesis P1: A \/ B.
Hypothesis P2: A -> C.
Hypothesis P3: B -> D.

Theorem dc: C \/ D.
dis_e (A \/ B) H1 H2.
exact P1.
dis_i1.
imp_e A.
exact P2.
exact H1.
dis_i2.
imp_e B.
exact P3.
exact H2.
Qed.