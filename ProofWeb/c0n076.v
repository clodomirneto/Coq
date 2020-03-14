Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: ~B.

Theorem c0n076 : ~(A /\ B).
Proof.
neg_i H1.
neg_e B.
exact P1.
con_e2 A.
exact H1.
Qed.