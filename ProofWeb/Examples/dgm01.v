Require Import ProofWeb.

Parameter A B C: Prop.

Hypothesis P1: B -> C.

Theorem jm01: A /\ B -> C.

Proof.
imp_i H1.
imp_e (B).
exact P1.
con_e2 (A).
exact H1.
Qed.
