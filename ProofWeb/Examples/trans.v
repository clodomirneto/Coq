Require Import ProofWeb.

Variables A B : Prop.

Theorem trans : (A -> B) <-> (~B -> ~A).
Proof.
iff_i Hab Hnbna.
imp_i Hnb.
neg_i Ha.
neg_e (B).
exact Hnb.
imp_e (A).
exact Hab.
exact Ha.
imp_i Ha.
PBC Hnb.
neg_e (A).
imp_e (~B).
exact Hnbna.
exact Hnb.
exact Ha.
Qed.