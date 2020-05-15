Require Import ProofWeb.

Variables A B : Prop.

Theorem com_or : (A \/ B) <-> (B \/ A).
Proof.
iff_i Hab Hba.
dis_e (A \/ B) Ha Hb.
exact Hab.
dis_i2.
exact Ha.
dis_i1.
exact Hb.
dis_e (B \/ A) Hb Ha.
exact Hba.
dis_i2.
exact Hb.
dis_i1.
exact Ha.
Qed.