Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: ((A \/ B) /\ (A \/ C)).

Theorem c0n039 : (A \/ (B /\ C)).
Proof.
dis_e (A \/ B) H1 H2.
con_e1 (A \/ C).
exact P1.
dis_i1.
exact H1.
dis_e (A \/ C) H3 H4.
con_e2 (A \/ B).
exact P1.
dis_i1.
exact H3.
dis_i2.
con_i.
exact H2.
exact H4.
Qed.