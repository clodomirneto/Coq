Require Import ProofWeb.

Variables A B : Prop.

Theorem com_and : (A /\ B) <-> (B /\ A).
Proof.
iff_i Hab Hba.
con_i.
con_e2 (A).
exact Hab.
con_e1 (B).
exact Hab.
con_i.
con_e2 (B).
exact Hba.
con_e1 (A).
exact Hba.
Qed.