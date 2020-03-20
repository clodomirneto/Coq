Require Import ProofWeb.

Variables A B C : Prop.

Theorem exp : ((A /\ B) -> C) <-> (A -> (B -> C)).
Proof.
iff_i Habc Habc'.
imp_i Ha.
imp_i Hb.
imp_e (A /\ B).
exact Habc.
con_i.
exact Ha.
exact Hb.
imp_i Hab.
imp_e (B).
imp_e (A).
exact Habc'.
con_e1 (B).
exact Hab.
con_e2 (A).
exact Hab.
Qed.