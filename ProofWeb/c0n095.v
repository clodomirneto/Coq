Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (A /\ B).

Theorem c0n095 : ~(~A \/ ~B).
Proof.
neg_i H1.
neg_e A.
dis_e (~A \/ ~B) H2 H3.
exact H1.
exact H2.
neg_i H4.
neg_e B.
exact H3.
con_e2 A.
exact P1.
con_e1 B.
exact P1.
Qed.