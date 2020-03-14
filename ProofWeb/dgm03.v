Require Import ProofWeb.

Parameter A B C: Prop.

Theorem dgm03: ((A -> C) /\ (B -> C)) -> (A \/ B) -> C.

Proof.
imp_i H1.
imp_i H2.
dis_e (A \/ B) H3 H4.
exact H2.
imp_e (A).
con_e1 (B -> C).
exact H1.
exact H3.
imp_e (B).
con_e2 (A -> C).
exact H1.
exact H4.
Qed.
