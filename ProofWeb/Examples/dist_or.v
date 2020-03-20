Require Import ProofWeb.

Variables A B C : Prop.

Theorem dist_or : (A \/ (B /\ C)) <-> ((A \/ B) /\ (A \/ C)).
Proof.
iff_i Habc Habc'.
dis_e (A \/ (B /\ C)) Ha Hbc.
exact Habc.
con_i.
dis_i1.
exact Ha.
dis_i1.
exact Ha.
con_i.
dis_i2.
con_e1 (C).
exact Hbc.
dis_i2.
con_e2 (B).
exact Hbc.
dis_e (A \/ B) Ha Hb.
con_e1 (A \/ C).
exact Habc'.
dis_i1.
exact Ha.
dis_e (A \/ C) Ha Hc.
con_e2 (A \/ B).
exact Habc'.
dis_i1.
exact Ha.
dis_i2.
con_i.
exact Hb.
exact Hc.
Qed.