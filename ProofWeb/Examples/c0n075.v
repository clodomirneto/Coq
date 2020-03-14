Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: ~A.

Theorem c0n075 : ~(A /\ B).
Proof.
neg_i H1.
neg_e A.
exact P1.
con_e1 B.
exact H1.
Qed.