Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: ((A /\ B) \/ (A /\ C)).

Theorem c0n037 : (A /\ (B \/ C)).
Proof.
dis_e ((A /\ B) \/ (A /\ C)) H1 H2.
exact P1.
con_i.
con_e1 B.
exact H1.
dis_i1.
con_e2 A.
exact H1.
con_i.
con_e1 C.
exact H2.
dis_i2.
con_e2 A.
exact H2.
Qed.