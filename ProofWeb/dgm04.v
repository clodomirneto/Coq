Require Import ProofWeb.

Parameter A B C: Prop.

Theorem dgm04: A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).

Proof.
imp_i H1.
dis_e (B \/ C) H2 H3.
con_e2 (A).
exact H1.
dis_i1.
con_i.
con_e1 (B \/ C).
exact H1.
exact H2.
dis_i2.
con_i.
con_e1 (B \/ C).
exact H1.
exact H3.
Qed.
