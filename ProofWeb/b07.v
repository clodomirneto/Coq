Require Import ProofWeb.

Parameter P Q : Prop.

Hypothesis P1 : ~P \/ ~Q.

Theorem b07 : ~(P /\ Q).

Proof.
dis_e (~P \/ ~Q) H1 H2.
exact P1.
neg_i H3.
neg_e (P).
exact H1.
con_e1 (Q).
exact H3.
neg_i H4.
neg_e (Q).
exact H2.
con_e2 (P).
exact H4.
Qed.
