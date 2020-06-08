Require Import ProofWeb.

Parameter A B C: Prop.

Theorem dgm05: A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).

Proof.
imp_i H1.
dis_e (A \/ (B /\ C)) H2 H3.
exact H1.
con_i.
dis_i1.
exact H2.
dis_i1.
exact H2.
con_i.
dis_i2.
con_e1 (C).
exact H3.
dis_i2.
con_e2 (B).
exact H3.
Qed.
