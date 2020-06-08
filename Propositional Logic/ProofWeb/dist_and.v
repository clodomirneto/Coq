Require Import ProofWeb.

Variables A B C : Prop.

Theorem dist_and : (A /\ (B \/ C)) <-> ((A /\ B) \/ (A /\ C)).
Proof.
iff_i Habc Habc'.
dis_e (B \/ C) Hb Hc.
con_e2 (A).
exact Habc.
dis_i1.
con_i.
con_e1 (B \/ C).
exact Habc.
exact Hb.
dis_i2.
con_i.
con_e1 (B \/ C).
exact Habc.
exact Hc.
dis_e ((A /\ B) \/ (A /\ C)) Hab Hac.
exact Habc'.
con_i.
con_e1 (B).
exact Hab.
dis_i1.
con_e2 (A).
exact Hab.
con_i.
con_e1 (C).
exact Hac.
dis_i2.
con_e2 (A).
exact Hac.
Qed.
