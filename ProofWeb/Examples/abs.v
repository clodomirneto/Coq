Require Import ProofWeb.

Parameter A B: Prop.

Hypothesis P1: A -> B.

Theorem abs: A -> (A /\ B).
Proof.
imp_i H1.
con_i.
exact H1.
imp_e A.
exact P1.
exact H1.
Qed.