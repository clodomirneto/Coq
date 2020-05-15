Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A \/ (B /\ C)).

Theorem c0n038 : ((A \/ B) /\ (A \/ C)).
Proof.
dis_e (A \/ (B /\ C)) H1 H2.
exact P1.
con_i.
dis_i1.
exact H1.
dis_i1.
exact H1.
con_i.
dis_i2.
con_e1 C.
exact H2.
dis_i2.
con_e2 B.
exact H2.
Qed.