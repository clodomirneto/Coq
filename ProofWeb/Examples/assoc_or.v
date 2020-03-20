Require Import ProofWeb.

Variables A B C : Prop.

Theorem assoc_or : (A \/ (B \/ C)) <-> ((A \/ B) \/ C).
Proof.
iff_i Habc Habc'.
dis_e (A \/ (B \/ C)) Ha Hbc.
exact Habc.
dis_i1.
dis_i1.
exact Ha.
dis_e (B \/ C) Hb Hc.
exact Hbc.
dis_i1.
dis_i2.
exact Hb.
dis_i2.
exact Hc.
dis_e ((A \/ B) \/ C) Hab Hc.
exact Habc'.
dis_e (A \/ B) Ha Hb.
exact Hab.
dis_i1.
exact Ha.
dis_i2.
dis_i1.
exact Hb.
dis_i2.
dis_i2.
exact Hc.
Qed.