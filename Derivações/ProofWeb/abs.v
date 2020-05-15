Require Import ProofWeb.

Variables A B : Prop.

Hypothesis P1 : A -> B.

Theorem abs : A -> (A /\ B).
Proof.
imp_i Ha.
con_i.
exact Ha.
imp_e (A).
exact P1.
exact Ha.
Qed.