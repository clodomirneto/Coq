Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (~A \/ ~B).

Theorem c0n097 : ~(A /\ B).
Proof.
neg_i H1.
neg_e (~A \/ ~B).
neg_i H2.
neg_e A.
dis_e (~A \/ ~B) H3 H4.
exact P1.
exact H3.
neg_i H5.
neg_e B.
exact H4.
con_e2 A.
exact H1.
con_e1 B.
exact H1.
exact P1.
Qed.