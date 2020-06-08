Require Import ProofWeb.

Variables A B C : Prop.

Theorem assoc_and : (A /\ (B /\ C)) <-> ((A /\ B) /\ C).
Proof.
iff_i Habc Habc'.
con_i.
con_i.
con_e1 (B /\ C).
exact Habc.
con_e1 (C).
con_e2 (A).
exact Habc.
con_e2 (B).
con_e2 (A).
exact Habc.
con_i.
con_e1 (B).
con_e1 (C).
exact Habc'.
con_i.
con_e2 (A).
con_e1 (C).
exact Habc'.
con_e2 (A /\ B).
exact Habc'.
Qed.