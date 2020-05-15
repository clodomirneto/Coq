Require Import ProofWeb.

Variables A B : Prop.

Theorem dm_and : (~(A /\ B)) <-> (~A \/ ~B).
Proof.
iff_i Hnab Hnanb.
PBC Hnnanb.
neg_e (A /\ B).
exact Hnab.
con_i.
PBC Hna.
neg_e (~A \/ ~B).
exact Hnnanb.
dis_i1.
exact Hna.
PBC Hnb.
neg_e (~A \/ ~B).
exact Hnnanb.
dis_i2.
exact Hnb.
dis_e (~A \/ ~B) Hna Hnb.
exact Hnanb.
neg_i Hab.
neg_e (A).
exact Hna.
con_e1 (B).
exact Hab.
neg_i Hab.
neg_e (B).
exact Hnb.
con_e2 (A).
exact Hab.
Qed.