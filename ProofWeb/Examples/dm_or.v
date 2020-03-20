Require Import ProofWeb.

Variables A B : Prop.

Theorem dm_or : ~(A \/ B) <-> (~A /\ ~B).
Proof.
iff_i Hnab Hnanb.
con_i.
neg_i Ha.
neg_e (A \/ B).
exact Hnab.
dis_i1.
exact Ha.
neg_i Hb.
neg_e (A \/ B).
exact Hnab.
dis_i2.
exact Hb.
neg_i Hab.
neg_e (A).
con_e1 (~B).
exact Hnanb.
dis_e (A \/ B) Ha Hb.
exact Hab.
exact Ha.
PBC Hna.
neg_e (B).
con_e2 (~A).
exact Hnanb.
exact Hb.
Qed.