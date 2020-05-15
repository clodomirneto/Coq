Require Import ProofWeb.

Variables A B : Prop.

Theorem im : (A -> B) <-> (~A \/ B).
Proof.
iff_i Hab Hnab.
PBC Hnnab.
neg_e (~A \/ B).
exact Hnnab.
dis_i1.
neg_i Ha.
neg_e (~A \/ B).
exact Hnnab.
dis_i2.
imp_e (A).
exact Hab.
exact Ha.
imp_i Ha.
dis_e (~A \/ B) Hna Hb.
exact Hnab.
PBC Hnb.
neg_e (A).
exact Hna.
exact Ha.
exact Hb.
Qed.